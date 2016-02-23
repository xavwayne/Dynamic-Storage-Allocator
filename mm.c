/*
 * mm.c
 *Name: Xiaoyu Wang  AndrewID:xiaoyuw
 * 
 * Segregetad List with Best Fit searching algorithm
 *
 *Each allocated block contains a header, a footer. If the block is free,
 *the payload area will contain information about the next free block and 
 *previous free block.
 *
 *All the free blocks, based on its size, will be added to an according 
 *free list. There are 10 free lists in all.
 *
 *When searching a fit from the free list, it searches almostly through the
 *free list. But considering the speed, when the fit counter goes beyond the 
 *STOP value, search will stop.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>


#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  168  /* Extend heap by this amount (bytes) */  
#define MINSIZE    24

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))   
#define PUTL(p,val)  (*(long *)(p)=(long)(val))
#define GETL(p)      (*(long *)(p))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                   

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

#define SET_NEXT(bp, next_ptr) PUTL(bp, next_ptr)
#define SET_PREV(bp, prev_ptr) PUTL((char *)(bp)+DSIZE, prev_ptr) //

 #define GET_NEXT(bp)  GETL(bp)
 #define GET_PREV(bp) GETL((char *)(bp)+DSIZE) 

 #define STOP 50





 /* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */  
 static char **free_listp=0; /*pointers to the free lists*/



/* Function prototypes for internal helper routines */
 static void *extend_heap(size_t words);
 static void place(void *bp, size_t asize);
 static void *find_fit(size_t asize);
 static void *coalesce(void *bp);
 static void printblock(void *bp); 
 static void checkheap(int verbose);
 static void checkblock(void *bp);
 static void addFirst(void *bp);
 static void remove_from_list(void *bp);
 static int sizeClass(size_t size);
static  int power(int a,int b);
/*
 * Initialize: initialize the heap to be ready for allocating and freeing
 *return -1 on error, 0 on success.
 */
 int mm_init(void) {

    if ((free_listp = mem_sbrk(10*DSIZE)) == (void *)-1) 
        return -1;
    for(int i=0;i<10;i++)
        free_listp[i]=NULL;


    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) 
       return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
   heap_listp += (2*WSIZE);                    



   if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
       return -1;

   return 0;
}

/*
 * malloc   simulating the lib malloc
 */
 void *malloc (size_t size) {


	size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      


    if (heap_listp == 0){
       mm_init();
   }

    /* Ignore spurious requests */
   if (size == 0)
       return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
   asize = MAX(ALIGN(size) + DSIZE, MINSIZE);

    /* Search the free list for a fit */
   if ((bp = find_fit(asize)) != NULL) {  
       place(bp, asize);                  

       return bp;
   }

    /* No fit found. Get more memory and place the block */
   extendsize = MAX(asize,CHUNKSIZE);                 
   if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
       return NULL;                                 
   place(bp, asize);   

   return bp;
   return NULL;
}

/*
 * free
 * free an given allocatate space
 */
 void free (void *ptr) {
    if(!ptr) return;
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size,0));
    PUT(FTRP(ptr), PACK(size,0));
    coalesce(ptr);
    
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  
 *      
 */
 void *realloc(void *oldptr, size_t size) {
   size_t oldsize;
   void *newptr;
   size_t asize = MAX(ALIGN(size) + DSIZE, MINSIZE);

    /* If size == 0 then this is just free, and we return NULL. */
   if(size == 0) {
       free(oldptr);
       return 0;
   }

    /* If oldptr is NULL, then this is just malloc. */
   if(oldptr == NULL) {
       return malloc(size);
   }

   oldsize = GET_SIZE(HDRP(oldptr));
   if(asize <= oldsize)
   {
      size = asize;

		/*if the remaining size can not hold a new block,
        *just return the block pointer*/
      if(oldsize - asize < MINSIZE)

         return oldptr;

     PUT(HDRP(oldptr), PACK(asize, 1));
     PUT(FTRP(oldptr), PACK(asize, 1));
     PUT(HDRP(NEXT_BLKP(oldptr)), PACK(oldsize-asize, 1));
     PUT(FTRP(NEXT_BLKP(oldptr)), PACK(oldsize-asize, 1));
     free(NEXT_BLKP(oldptr));
     return oldptr;
 }

 newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
 if(!newptr) {
   return 0;
}

    /* Copy the old data. */
oldsize = GET_SIZE(HDRP(oldptr));
if(size < oldsize) oldsize = size;
memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
free(oldptr);

return newptr;

}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
 void *calloc (size_t nmemb, size_t size) {
     // printf("in calloc\n");
   size_t bytes = nmemb * size;
   void *newptr;

   newptr = malloc(bytes);
   memset(newptr, 0, bytes);

   return newptr;

}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
 /*
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}
*/

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
 /*
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}*/

/*
 * mm_checkheap
 */
 void mm_checkheap(int lineno) {
   checkheap(lineno);

}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
 static void *extend_heap(size_t words) 
 {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if (size < MINSIZE)
        size = MINSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)  
       return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 

    // mm_checkheap(1);
    /* Coalesce if the previous block was free */
   return coalesce(bp);                                          

    // mm_checkheap(1);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
 static void *coalesce(void *bp) 
 {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
    addFirst(bp);
    return bp;
}

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
    remove_from_list(NEXT_BLKP(bp)); //remove next block from free list
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size,0));
    addFirst(bp);
}

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
remove_from_list(PREV_BLKP(bp));
size += GET_SIZE(HDRP(PREV_BLKP(bp)));
PUT(FTRP(bp), PACK(size, 0));
PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
bp = PREV_BLKP(bp);
addFirst(bp);
}

    else {                                     /* Case 4 */
remove_from_list(PREV_BLKP(bp));
remove_from_list(NEXT_BLKP(bp)); 
size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
GET_SIZE(FTRP(NEXT_BLKP(bp)));
PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
bp = PREV_BLKP(bp);
addFirst(bp);
}

return bp;
}

/**
* xiaoyuw defined functions helper functions
*/


/**
*sizeClass - compute the belonging free list according to the size
*
*/
static int sizeClass(size_t size){
    if(size<=16)
        return 0;
    else if(size<=32)
        return 1;
    else if(size<=64)
        return 2;
    else if(size<=128)
        return 3;
    else if(size<=256)
        return 4;
    else if(size<=512)
        return 5;
    else if(size<=1024)
        return 6;
    else if(size <=2048)
        return 7;
    else if (size <=4096)
        return 8;
    
    else 
        return 9;

}


/**
*addFirst - add a free block to a proper free list 
*/
static void addFirst(void *bp){
    size_t size=GET_SIZE(HDRP(bp));
    int index=sizeClass(size);

    SET_NEXT(bp,free_listp[index]);
    SET_PREV(bp,NULL);
    if(free_listp[index]!=NULL){
      SET_PREV(free_listp[index],bp);
  }
  free_listp[index]=(char *)bp;
}

/**
*remove_from_list - remove a free block from its list
*/
static void remove_from_list(void *bp){

    size_t size=GET_SIZE(HDRP(bp));
    int index=sizeClass(size);

    if(GET_PREV(bp)!=0)
        SET_NEXT(GET_PREV(bp),GET_NEXT(bp));
    else
    	free_listp[index]=(char *)GET_NEXT(bp);
    if(GET_NEXT(bp)!=0)
     SET_PREV(GET_NEXT(bp),GET_PREV(bp));

}

/**
*find_fit - find the best fit free block. However this "best fit" 
* does not go though the entire list, instead, it stops at certain
*condition, for the sake of efficiency
*/
static void *find_fit(size_t asize){

  void *bp;
  void *best=NULL;
     int flag=0;  //mark if the best fit was founded in the list
     int count=0;

     int index=sizeClass(asize);// determine size class
     for(int i=index;i<10;i++){
        for (bp = free_listp[i]; bp!=NULL; bp = (char *) GET_NEXT(bp)) {
            if  (asize <= GET_SIZE(HDRP(bp)) && !flag){
                best=bp;
                flag=1;
            }
            else if  ( flag && asize <= GET_SIZE(HDRP(bp))
             && GET_SIZE(HDRP(bp))<=GET_SIZE(HDRP(best))) {
                count++;
                best=bp;
                if(count>=STOP)
                    return best;
            }
        }

        if(flag)
           return best;
   }
    return NULL; /* No fit */
}

/**
*place - allocate certain space from the block, split it conditionally.
*/
static void place(void *bp, size_t asize){

    remove_from_list(bp);//remove this free space from free list
    size_t csize = GET_SIZE(HDRP(bp));   

    if ((csize - asize) >= (MINSIZE)) { 
       PUT(HDRP(bp), PACK(asize, 1));
       PUT(FTRP(bp), PACK(asize, 1));
       bp = NEXT_BLKP(bp);
       PUT(HDRP(bp), PACK(csize-asize, 0));
       PUT(FTRP(bp), PACK(csize-asize, 0));
	addFirst(bp); //add new spliced block to proper free list
}
else { 
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
}
mm_checkheap(0);
}


/**
* checkers
*/

/**
* printblock - show block information
*/
static void printblock(void *bp) 
{
    int hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
       printf("%p: EOL\n", bp);
       return;
   }
    
     if (halloc)
        printf("%p: header:[%d:%c] footer:[%d:%c]\n", bp,
        hsize, (halloc ? 'a' : 'f'),fsize, (falloc ? 'a' : 'f'));
            
    else
        printf("%p:header:[%d:%c] prev:%ld next:%ld footer:[%d:%c]\n",
        bp, hsize, (halloc ? 'a' : 'f'), GET_PREV(bp),GET_NEXT(bp),
         fsize, (falloc ? 'a' : 'f'));
            
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
       printf("Error: %p is not doubleword aligned\n", bp);
   if (GET(HDRP(bp)) != GET(FTRP(bp)))
       printf("Error: header does not match footer\n");
}

/* 
 * checkheap - Minimal check of the heap for consistency 
 */
 void checkheap(int verbose) 
 {
    char *bp = heap_listp;
    char **flp=free_listp;
    char *lp;
    int freecount1=0;
    int freecount2=0;

    if (verbose)
       printf("Heap (%p):\n", heap_listp);

   if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
       printf("Bad prologue header\n");
   checkblock(heap_listp);

   for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
       if (verbose) 
           printblock(bp);
       checkblock(bp);
       if(!GET_ALLOC(HDRP(heap_listp)))
        freecount2++;
   }

   if (verbose)
       printblock(bp);
   if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
       printf("Bad epilogue header\n");

   
    for(int i=0;i<10;i++){
        lp=flp[i];
        if((long)lp>(long)mem_heap_hi() || (long)lp<(long)mem_heap_lo())   //check free list pointers
            printf("pointer:%p out of boundary\n", lp);

        for(;lp!=NULL;lp=(char*)GET_NEXT(lp)){   //check if previous and next adjacent
            char *next=(char*)GET_NEXT(lp);
            if( next!=NULL && lp!=(char*)GET_PREV(next)){
                printf("free list not consistency next and previous!\n");                
            }

            if((int)GET_SIZE(HDRP(lp)) > power(2,i+4) || (int)GET_SIZE(HDRP(lp)) < power(2,i+3) )
                printf("Wrong bucket size range!\n");
            freecount1++;
        }

    }

    if(freecount1!=freecount2)  //check free block numbers
        printf("free count numbers are not consistent!\n");


}

static  int power(int a,int b){
    int c=1;
    for(int i=0;i<b;i++){
        c=c*a;
    }
    return c;
}