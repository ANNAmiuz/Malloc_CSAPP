/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "nicole",
    /* Second member's email address (leave blank if none) */
    "119010114@link.cuhk.edu.cn"};

//CONSTANTS
#define SPLIT                                                        /* Split or not in realloc */
#define DEBUGx                                                       /* Debug mode or not */
#define WSIZE 4 /* Word and header/footer size (bytes) */            //line:vm:mm:beginconst
#define DSIZE 8                                                      /* Double word size (bytes) */
#define ALIGNMENT 8                                                  /* single word (4) or double word (8) alignment */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */ //line:vm:mm:endconst
#define MINBLOCKSIZE 16                                              /* Minimum block size of is 16 byetes: 4 words */
#define SEGLEN 15                                                    /* Odd number, the last size range is [2^18, ~] */

//MACORS
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) /* rounds up to the nearest multiple of ALIGNMENT */

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define PRED(bp) ((char *)bp)
#define SUCC(bp) ((char *)bp + WSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

// Global variables
static char *heap_base = 0;  /* Pointer to the heap base */
static char *heap_listp = 0; /* Pointer to first block */

/* Function prototypes for internal helper routines */
static int get_classidx(size_t asize);
static void *extend_heap(size_t words);
static void* place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void insert_free_block(void *bp); //argu: start of the payload
static void delete_free_block(void *bp);
static void printblock(void *bp);
static void checkheap(int verbose);
static void checkblock(void *bp);

static void mm_check(void);
static void error_reporter(char *bp, char *__ERROR_MSG__);
static void print_funcname(char *name);
static void print_heap_list(char *__FUNCNAME__);
static void print_block_info(char *bp, char *__FUNCNAME__);
static void print_free_list(char *__FUNCNAME__);
static void show_free_link(char *root);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
#ifdef DEBUG
    printf("mm_init() invoked. \n");
#endif
    if ((heap_base = mem_sbrk((SEGLEN + 3) * WSIZE)) == (void *)-1)
        return -1;
#ifdef DEBUG
    printf("base: %u. \n", heap_base);
#endif
    //pointer to the segregated list
    int i;
    for (i = 0; i < SEGLEN; i++)
    {
        PUT(heap_base + i * WSIZE, 0);
    }

    //prologue block
    PUT(heap_base + (i + 0) * WSIZE, PACK(DSIZE, 1));
    PUT(heap_base + (i + 1) * WSIZE, PACK(DSIZE, 1));
    //epilogue block
    PUT(heap_base + (i + 2) * WSIZE, PACK(0, 1));

    heap_listp = heap_base + (i + 1) * WSIZE;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

#ifdef DEBUG
    mm_check();
#endif
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
#ifdef DEBUG
    printf("mm_malloc() invoked. \n");
#endif
    if (heap_listp == NULL)
        mm_init();
    if (size == 0)
        return NULL;
    int newsize = MAX(ALIGN(size + SIZE_T_SIZE), 2 * DSIZE);
    void *bp;
    if ((bp = find_fit(newsize)) != NULL)
    {
#ifdef DEBUG
        //print_block_info(bp, "find_fit");
#endif
        bp = place(bp, newsize);
        return bp;
    }
    size_t extend_size = MAX(newsize, CHUNKSIZE);
    if ((bp = (extend_heap(extend_size / WSIZE))) == NULL)
    {
        return (void *)(-1);
    }
    bp = place(bp, newsize);
#ifdef DEBUG
    mm_check();
#endif
    return bp;
}

/*
 * mm_free - Freeing a block, coalescing.
 */
void mm_free(void *ptr)
{
#ifdef DEBUG
    printf("mm_free() invoked. \n");
#endif
    if (heap_listp == NULL)
        mm_init();
    if (ptr == NULL)
        return NULL;
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    PUT(PRED(ptr), NULL);
    PUT(SUCC(ptr), NULL);
    coalesce(ptr);
#ifdef DEBUG
    mm_check();
#endif
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
#ifdef DEBUG
    printf("mm_realloc() invoked. \n");
#endif
    void *oldptr = ptr;
    void *newptr;
    void *bp;
    size_t copySize;

    if (ptr == NULL)
        return mm_malloc(size);
    else if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }
    size_t asize = ALIGN(size + SIZE_T_SIZE);
    size_t oldsize = GET_SIZE(HDRP(ptr));
    size_t next_blocksize = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    copySize = MIN(asize, oldsize) - SIZE_T_SIZE;

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));

    //new size < old size, split
    //the front part is allocated, the back part remainder is free?
    if (asize < oldsize)
    {
#ifdef SPLIT
        if (!next_alloc)
        {
            delete_free_block(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));
            ptr = NEXT_BLKP(ptr);
            PUT(HDRP(ptr), PACK(oldsize - asize + next_blocksize, 0));
            PUT(FTRP(ptr), PACK(oldsize - asize + next_blocksize, 0));
            PUT(PRED(ptr), NULL);
            PUT(SUCC(ptr), NULL);
            return oldptr;
        }
        else
        {
            if (oldsize - asize >= MINBLOCKSIZE)
            {
                PUT(HDRP(ptr), PACK(asize, 1));
                PUT(FTRP(ptr), PACK(asize, 1));
                ptr = NEXT_BLKP(ptr);
                PUT(HDRP(ptr), PACK(oldsize - asize, 0));
                PUT(FTRP(ptr), PACK(oldsize - asize, 0));
                PUT(PRED(ptr), NULL);
                PUT(SUCC(ptr), NULL);
                size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
                size_t size = oldsize - asize;
                if (!next_alloc)
                {
                    size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
                    delete_free_block(NEXT_BLKP(ptr));
                    PUT(HDRP(ptr), PACK(size, 0));
                    PUT(FTRP(ptr), PACK(size, 0));
                    PUT(PRED(ptr), NULL);
                    PUT(SUCC(ptr), NULL);
                }
                insert_free_block(ptr);
            }
        }
#endif

#ifdef DEBUG
        mm_check();
#endif

        return oldptr;
    }
    //same size, return directly
    else if (asize == oldsize)
        return oldptr;
    //the next block is free
    else if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) && asize <= next_blocksize + oldsize)
    {
        delete_free_block(NEXT_BLKP(ptr));
        if (next_blocksize + oldsize - asize >= MINBLOCKSIZE)
        {
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));
            ptr = NEXT_BLKP(ptr);
            PUT(HDRP(ptr), PACK(next_blocksize + oldsize - asize, 0));
            PUT(FTRP(ptr), PACK(next_blocksize + oldsize - asize, 0));
            PUT(PRED(ptr), NULL);
            PUT(SUCC(ptr), NULL);
            insert_free_block(ptr);
        }
        else
        {
            PUT(HDRP(ptr), PACK(oldsize + next_blocksize, 1));
            PUT(FTRP(ptr), PACK(oldsize + next_blocksize, 1));
        }
#ifdef DEBUG
        mm_check();
#endif
        return oldptr;
    }
    //the realloced block at the top of the heap
    else if (next_blocksize == 0)
    {
        if (((long)(bp = mem_sbrk(asize - oldsize))) == -1)
            return NULL;
        PUT(HDRP(oldptr), PACK(asize, 1));
        PUT(FTRP(oldptr), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(oldptr)), PACK(0, 1));
#ifdef DEBUG
        mm_check();
#endif
        return oldptr;
    }
    //malloc a new area
    else
    {
        newptr = mm_malloc(size);
        memcpy(newptr, oldptr, copySize);
        PUT(HDRP(oldptr), PACK(oldsize, 0));
        PUT(FTRP(oldptr), PACK(oldsize, 0));
        PUT(PRED(oldptr), NULL);
        PUT(SUCC(oldptr), NULL);
        coalesce(oldptr);
#ifdef DEBUG
        mm_check();
#endif
        return newptr;
    }
}

static void print_funcname(char *name)
{
    printf("In %s\n", name);
}

static void print_heap_list(char *__FUNCNAME__)
{
    printf("-----------===  Block List ===--------------\n");
    print_funcname(__FUNCNAME__);
    char *bp = heap_listp;
    while (GET_ALLOC(HDRP(bp)) != 1 || GET_SIZE(HDRP(bp)) != 0)
    {
        if (!GET_ALLOC(HDRP(bp)) && !CRT_BLKSZ(bp))
        {
            Error_Handler(bp, "Heap Last Pointer Leak!!!\n");
            exit(-1);
        }
        printf("Block Pointer: %p \t Allocated: %d \t Size: %d\n", bp, GET_ALLOC(HDRP(bp)), GET_SIZE(HDRP(bp)));
        bp = NEXT_BLKP(bp);
    }
    printf("Block Pointer: %p \t Allocated: %d \t Size: %d\n", bp, GET_ALLOC(HDRP(bp)), GET_SIZE(HDRP(bp)));
    printf("----------------------------------------------------\n\n");
}

/* Display the block info & invoking func name by pointer bp. Allocated: Header & Footer size  |  Free: Class Index, root pointer, Pred&Succ block*/
static void print_block_info(char *bp, char *__FUNCNAME__)
{
    printf("-------------=== BLOCK INFO ===----------------\n");
    print_funcname(__FUNCNAME__);
    printf("Pointer: %p\n", bp);
    char *__STATE__ = GET_ALLOC(HDRP(bp)) == 1 ? "ALLOCATED" : "FREE";
    printf("STATE: %s \t Header_SIZE: %d \t Footer_SIZE: %d\n", __STATE__, GET_SIZE(HDRP(bp)), GET_SIZE(FTRP(bp)));
    if (!GET_ALLOC(HDRP(bp)))
    {
        int classidx = get_classidx(GET_SIZE(HDRP(bp)));
        char *root = heap_base + classidx * WSIZE;
        printf("ClassIdx: %u, ROOT: %p\n", classidx, root);
        if ((void *)GET(PRED(bp)))
            printf("PRED_BLOCKP: %p \t", (void *)GET(PRED(bp)));
        else
            printf("PRED_BLKP: NULL \t");
        if ((void *)GET(SUCC(bp)))
            printf("SUCC_BLOCKP: %p \n", (void *)GET(SUCC(bp)));
        else
            printf("SUCC_BLKP: NULL \n");
    }
    printf("----------------------------------------------------\n\n");
}

/* Display all the free blocks info & the invoking function name: state, root, size*/
static void print_free_list(char *__FUNCNAME__)
{
    printf("-------------=== FREE BLOCK LIST ===----------------\n");
    print_funcname(__FUNCNAME__);
    int seg_idx = 0;

    while (seg_idx < SEGLEN)
    {
        char *root = heap_base + seg_idx * WSIZE;
        char *bp = GET(root);
        while (bp)
        {
            char *__STATE__ = GET_ALLOC(HDRP(bp)) == 1 ? "ALLOCATED" : "FREE";
            printf("bp: %p \t IDX: %d ROOT: %p \t STATE: %s \t SIZE: %d \t", bp, seg_idx, root, __STATE__, GET_SIZE(HDRP(bp)));

            if (!GET_ALLOC(HDRP(bp)))
            {
                if ((void *)GET(PRED(bp)))
                    printf("PRED_BLOCKP: %p \t", (void *)GET(PRED(bp)));
                else
                    printf("PRED_BLKP: NULL \t");
                if ((void *)GET(SUCC(bp)))
                    printf("SUCC_BLOCKP: %p \n", (void *)GET(SUCC(bp)));
                else
                    printf("SUCC_BLKP: NULL \n");
            }
            bp = GET(SUCC(bp));
        }
        seg_idx++;
    }

    printf("----------------------------------------------------\n\n");
}

static void show_free_link(char *root)
{
    if (SUCC_BLKP(root))
        printf("ROOT: %p --> ", root);
    else
    {
        printf("ROOT: %p\n", root);
        return;
    }
    char *succ = (char *)SUCC_BLKP(root);
    while (SUCC_BLKP(succ))
    {
        printf("%p ---> ", succ);
        succ = (char *)SUCC_BLKP(succ);
    }
    printf("%p\n", succ);
}

/* Display the error message and the error block info*/
static void error_reporter(char *bp, char *__ERROR_MSG__)
{
    printf("%s", __ERROR_MSG__);
    print_block_info(bp, "Error");
}

/* mm_check: check the whole memory */
static void mm_check()
{
    //start from the prologue block
    char *cur_block = heap_listp;

    //end at the epilogue block
    while (GET_SIZE(HDRP(NEXT_BLKP(cur_block))) != 0)
    {
        // header ==  footer ?
        if (GET_SIZE(HDRP(cur_block)) != GET_SIZE(FTRP(cur_block)) ||
            GET_ALLOC(HDRP(cur_block)) != GET_ALLOC(FTRP(cur_block)))
            error_reporter(cur_block, "Header and Footer Mismatch\n");
        // coalescing ?
        if (!GET_ALLOC(HDRP(cur_block)))
        {
            if (!GET_ALLOC(HDRP(PREV_BLKP(cur_block))))
                error_reporter(cur_block, "PREV Coalescing Error\n");
            if (!GET_ALLOC(HDRP(NEXT_BLKP(cur_block))))
                error_reporter(cur_block, "NEXT Coalescing Error\n");
        }
        cur_block = NEXT_BLKP(cur_block);
    }

    // allocated block in free list?
    int seg_idx;
    for (seg_idx = 0; seg_idx < SEGLEN; seg_idx++)
    {
        cur_block = GET(heap_base + seg_idx * WSIZE);
        while (cur_block)
        {
            if (GET_ALLOC(HDRP(cur_block)))
                error_reporter(cur_block, "Allocated Block in Free List\n");
            cur_block = GET(SUCC(cur_block));
        }
    }
}

/* 
 * The remaining routines are internal helper routines 
 */

/*
 * get_classidx - get the class index by asize
*/
static int get_classidx(size_t asize)
{
    int class_idx = 0;
    asize >>= 4;
    while (asize)
    {
        asize >>= 1;
        class_idx++;
    }

    class_idx = ((class_idx > SEGLEN - 1) ? SEGLEN - 1 : class_idx);
    return class_idx;
}

/*
 * insert_free_block - insert a free block by bp (pointer of payload)
*/
static void insert_free_block(void *bp)
{
#ifdef DEBUG
    printf("insert_free_block() invoked. \n");
#endif
    int class_idx = get_classidx(GET_SIZE(HDRP(bp)));
    void *root = heap_base + class_idx * WSIZE;
    void *cur = GET(root);
    void *prev;
    if (cur == NULL)
        PUT(root, bp);
    //ordered by value of address
    else
    {
        while ((unsigned int)cur < (unsigned int)bp)
        {
            if (GET(SUCC(cur)) != NULL)
            {
                cur = GET(SUCC(cur));
            }
            //insert at the tail
            else
            {
                PUT(SUCC(cur), bp);
                PUT(PRED(bp), cur);
                PUT(SUCC(bp), NULL);
#ifdef DEBUG
                mm_check();
#endif
                return;
            }
        }
        //cur is the start of linkedlist
        if (cur == GET(root))
        {
            PUT(root, bp);
            PUT(SUCC(bp), cur);
            PUT(PRED(bp), NULL);
            PUT(PRED(cur), bp);
        }
        //cur is in the middle of the linkedlist
        else
        {
            prev = GET(PRED(cur));
            PUT(SUCC(bp), cur);
            PUT(PRED(cur), bp);
            PUT(PRED(bp), prev);
            PUT(SUCC(prev), bp);
        }
    }
#ifdef DEBUG
    mm_check();
#endif
}

/*
 * delete_free_block - delete a free block by bp (pointer of payload)
*/
static void delete_free_block(void *bp)
{
#ifdef DEBUG
    printf("delete_free_block() invoked. \n");
    //print_block_info(bp, "delete_free_block");
#endif
    void *prev_bp = NULL;
    void *next_bp = NULL;
    int class_idx = get_classidx(GET_SIZE(HDRP(bp)));
    void *root = heap_base + class_idx * WSIZE;
    if (GET(PRED(bp)) && GET(SUCC(bp)))
    {
        prev_bp = GET(PRED(bp));
        next_bp = GET(SUCC(bp));
        PUT(SUCC(prev_bp), next_bp);
        PUT(PRED(next_bp), prev_bp);
    }
    else if (GET(PRED(bp)) && !GET(SUCC(bp)))
    {
        prev_bp = GET(PRED(bp));
        PUT(SUCC(prev_bp), NULL);
    }
    else if (!GET(PRED(bp)) && GET(SUCC(bp)))
    {
        next_bp = GET(SUCC(bp));
        PUT(root, next_bp);
        PUT(PRED(next_bp), NULL);
    }
    else
    {
        PUT(root, NULL);
    }
#ifdef DEBUG
    //mm_check();
#endif
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words)
{
#ifdef DEBUG
    printf("extend_heap() invoked. \n");
#endif

    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/* 
 * coalesce - Provide the start of payload bp, insert to sergregated list
 *            Return the new start of payload for the coalesced free block 
*/
static void *coalesce(void *bp)
{
#ifdef DEBUG
    printf("coalesce() invoked. \n");
    //print_block_info(bp, "coalesce");
    //print_block_info(NEXT_BLKP(bp), "coalesce");
    //print_block_info(PREV_BLKP(bp), "coalesce");
#endif
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    { /* Case 1 */
#ifdef DEBUG
        printf("Case 1. \n");
#endif
        PUT(PRED(bp), NULL);
        PUT(SUCC(bp), NULL);
        insert_free_block(bp);
#ifdef DEBUG
        mm_check();
#endif
        return bp;
    }

    else if (prev_alloc && !next_alloc)
    { /* Case 2 */
#ifdef DEBUG
        printf("Case 2. \n");
#endif
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        delete_free_block(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(PRED(bp), NULL);
        PUT(SUCC(bp), NULL);
        insert_free_block(bp);
#ifdef DEBUG
        mm_check();
#endif
        return bp;
    }

    else if (!prev_alloc && next_alloc)
    { /* Case 3 */
#ifdef DEBUG
        printf("Case 3. \n");
        //mm_check();
        //print_block_info(PREV_BLKP(bp), "coalesce1");
#endif
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        delete_free_block(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        PUT(PRED(bp), NULL);
        PUT(SUCC(bp), NULL);
#ifdef DEBUG
        //print_block_info(bp, "coalesce2");
        //print_block_info(NEXT_BLKP(bp), "coalesce2");
#endif
        insert_free_block(bp);
#ifdef DEBUG
        mm_check();
#endif
        return bp;
    }

    else
    { /* Case 4 */
#ifdef DEBUG
        printf("Case 4. \n");
#endif
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        delete_free_block(PREV_BLKP(bp));
        delete_free_block(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        PUT(PRED(bp), NULL);
        PUT(SUCC(bp), NULL);
        insert_free_block(bp);
#ifdef DEBUG
        mm_check();
#endif
        return bp;
    }
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void* place(void *bp, size_t asize)
{
#ifdef DEBUG
    printf("place() invoked. \n");
    //print_block_info(bp, "place");
    mm_check();
#endif
    size_t csize = GET_SIZE(HDRP(bp));
    delete_free_block(bp);
    if ((csize - asize) >= MINBLOCKSIZE)
    {
        //the allocated block is large relatively
        if (csize <= 10 * asize)
        {
            PUT(HDRP(bp), PACK(csize-asize, 0));
            PUT(FTRP(bp), PACK(csize-asize, 0));
            PUT(PRED(bp), NULL);
            PUT(SUCC(bp), NULL);
            insert_free_block(bp);
            bp = NEXT_BLKP(bp);
            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));
            return bp;
        }
        //the allocated block is small relatively
        else
        {
            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));
            void * oldptr = bp;
            bp = NEXT_BLKP(bp);
            PUT(HDRP(bp), PACK(csize - asize, 0));
            PUT(FTRP(bp), PACK(csize - asize, 0));
            PUT(PRED(bp), NULL);
            PUT(SUCC(bp), NULL);
            insert_free_block(bp);
            return oldptr;
        }
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        return bp;
    }
#ifdef DEBUG
    mm_check();
#endif
}

/* 
 * find_fit - Find a fit for a block with asize bytes (first-fit)
 */
static void *find_fit(size_t asize)
{
#ifdef DEBUG
    printf("find_fit() invoked. \n");
#endif
    int class_idx = get_classidx(asize);
    void *res;
    void *root;
    while (class_idx < SEGLEN)
    {
        root = heap_base + class_idx * WSIZE;
        res = GET(root);
        while (res)
        {
            if (GET_SIZE(HDRP(res)) >= asize)
            {
                return res;
            }
            res = GET(SUCC(res));
        }
        class_idx++;
    }
    return NULL; /* No fit */
}

static void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0)
    {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp,
           hsize, (halloc ? 'a' : 'f'),
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

    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (verbose)
            printblock(bp);
        checkblock(bp);
    }

    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}
