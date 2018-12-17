/*
 ******************************************************************************
 *                               mm-baseline.c                                *
 *           64-bit struct-based implicit free list memory allocator          *
 *                  15-213: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                     insert your documentation here. :)                     *
 *                                                                            *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
//#define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (8 bytes)
static const size_t dsize = 2*wsize;          // double word size (16 bytes)
static const size_t min_block_size = 2*dsize; // Minimum block size (32 bytes)
static const size_t chunksize = (1 << 6);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;
static const word_t align_mask = 0xF;           // 16  alignment

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    char payload[0];
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;


/* Global variables */
/* Pointer to first block */
static block_t *heap_start = NULL;
static int counter_malloc = 0;


bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *find_fit_N(size_t asize,int N);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

/*new helper functions*/
static void set_head_node(block_t *first_free_blk);
static void set_tail_node(block_t *last_free_blk);
static block_t * get_head(void);
static block_t * get_tail(void);

static block_t * get_prev_fblk(block_t * blk);
static block_t * get_next_fblk(block_t * blk);
static void set_prev_fblk(block_t * blk, block_t* prev);
static void set_next_fblk(block_t * blk, block_t* next);

//insert a new free block at head
static void insert_at_head(block_t * blk);
//remove a block from list, and reconnect the list
static void remove_fblk(block_t * blk);

block_t* get_heap_top_blk()
{

    size_t blksize = extract_size(   *((word_t*)(mem_heap_hi()-8-7))    );

    return (block_t*) (  (mem_heap_hi()-7)-blksize - 8);
}


//if LIFO
static void insert_at_head(block_t * blk)
{
    block_t* old_head = get_head();
    if(old_head==NULL){//list is empty
        set_head_node(blk);
        set_tail_node(blk);
    }else{ // list non_empty
        set_head_node(blk);
        set_next_fblk(blk,old_head);
        set_prev_fblk(old_head,blk);
    }
    return;
}
/////////////////////////////////////////////
//if FIFO
static void insert_at_tail(block_t * blk)
{
    block_t* old_tail = get_tail();
    if(old_tail==NULL){//list is empty
        set_head_node(blk);
        set_tail_node(blk);
    }else{ // list non_empty
        set_tail_node(blk);
        set_prev_fblk(blk,old_tail);
        set_next_fblk(old_tail,blk);
    }
    return;
}

static void remove_fblk(block_t * blk)
{
    if(blk==NULL){
        dbg_printf("Trying to remove a NULL pointer\n");
        return;
    }

    block_t * prev_fblk = get_prev_fblk(blk);
    block_t * next_fblk = get_next_fblk(blk);

    if(prev_fblk==NULL){// blk is the first free block in list
        set_head_node(next_fblk);
    }else{
        set_next_fblk(prev_fblk,next_fblk);
    }
    if(next_fblk==NULL){// blk is the last free block in list
        set_tail_node(prev_fblk);
    }else{
        set_prev_fblk(next_fblk,prev_fblk);
    }

    //clear prev and next pointers, easier for debugging
    //set_prev_fblk(blk, NULL);
    //set_next_fblk(blk, NULL);
    return;
}




static block_t * get_prev_fblk(block_t * blk)
{
    if(blk==NULL){
        dbg_printf("can not get_prev_fblk for a NULL pointer\n");
        exit(1);
    }
    return (block_t *)(*((word_t*)blk+1));
}

static block_t * get_next_fblk(block_t * blk)
{
    if(blk==NULL){
        dbg_printf("can not get_next_fblk for a NULL pointer\n");
        exit(1);
    }
    return (block_t *)(*((word_t*)blk+2));
}
static void set_prev_fblk(block_t * blk, block_t *prev)
{
    if(blk==NULL){
        dbg_printf("can not set_prev_fblk for a NULL pointer\n");
        exit(1);
    }
    ((block_t **)((word_t*)blk+1))[0] = prev;
}
static void set_next_fblk(block_t * blk, block_t *next)
{
    if(blk==NULL){
        dbg_printf("can not set_next_fblk for a NULL pointer\n");
        exit(1);
    }
    ((block_t **)((word_t*)blk+2))[0] = next;
}


/* new helper function definitions */
static void set_head_node(block_t *first_free_blk)
{
    ((block_t **)((word_t *)heap_start -3))[0] = first_free_blk;
    if(first_free_blk!=NULL){
        set_prev_fblk(first_free_blk, NULL);
    }
}

static void set_tail_node(block_t *last_free_blk)
{
    ((block_t **)((word_t *)heap_start -2))[0]= last_free_blk;
    if(last_free_blk!=NULL){
        set_next_fblk(last_free_blk, NULL);
    }
}

static block_t * get_head(void)
{
    return (block_t *) (*((word_t *)heap_start -3));
}

static block_t * get_tail(void)
{
    return (block_t *) (*((word_t *)heap_start -2));
}


static void show_heap(int size_word){
    int i = size_word;
    dbg_printf("index \t address \t value\n");
    for(i = 0; i<20; i++){
        dbg_printf("[%d] 0x%x \t| 0x%x\n",i, (unsigned int)((word_t*)heap_start-3+i), (unsigned int)((word_t*)heap_start-3+i)[0]);
        if(i==2)dbg_printf("----------------------------------------------------------------\n");
    }
}



/*
 * <what does mm_init do?>
 */
bool mm_init(void)
{
    dbg_printf("mm_init called\n");



    // Create the initial empty heap
    // first assign space to the head and tail nodes
    block_t **head_tail = (block_t**)(mem_sbrk(2*wsize));
    if (head_tail == (void *)-1)
    {
        return false;
    }
    head_tail[0] = (block_t *) NULL;            // pointer to the first free block
    head_tail[1] = (block_t *) NULL;            // pointer to the last free block.

    // assign space to header and footer
    word_t *start = (word_t *)(mem_sbrk(2*wsize));
    if (start == (void *)-1)
    {
        return false;
    }
    start[0] = pack(0, true); // Prologue footer
    start[1] = pack(0, true); // Epilogue header

    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }

/*
    dbg_printf("================================init called===================================\n");
    show_heap(20);
    dbg_printf("=============================================================================\n");
*/
    //exit(0);


    return true;
}

/*
 * <what does mmalloc do?>
 */
void *malloc(size_t size)
{
/*
    dbg_printf("================================malloc called===================================\n");
    show_heap(20);
    dbg_printf("=============================================================================\n");
*/

    dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        dbg_printf("================mm_init called inside malloc =========\n");
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    // header | prev | next | footer,        a total of 4 words
    if(size<=dsize){
        asize = 2*dsize;
    }else{
        asize = round_up(size+dsize, dsize);
    }


    // Search the free list for a fit
//    block = find_fit(asize);
    block = find_fit_N(asize,1E2);


    // note: the logic here is problematic. if the block at the current heap
    // top is free, but not big enough, the heap is still going to be extended by
    // asize/chunksize. This will introduce waste of space. Low utility. 

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {
        block_t* heap_top_block = get_heap_top_blk();
        if(!get_alloc(heap_top_block)){
            printf("extend size reduced by %d\n",(int)get_size(heap_top_block));
            asize = asize - get_size(heap_top_block);
            //printf("extend size reduced by %d\n",(int)get_size(heap_top_block));
        }

        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }

    }

    place(block, asize);            // conceptually put data into free block
    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));

    counter_malloc++;

    dbg_printf("================================ malloc %d finished===================================\n",counter_malloc);
    //show_heap(20);
    dbg_printf("=============================================================================\n");


    //if(counter_malloc==2)exit(1);

    return bp;
}

/*
 * <what does free do?>
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        dbg_printf("freeing a null pointer, quit\n");
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);
    write_header(block, size, false);
    write_footer(block, size, false);

    coalesce(block);

    dbg_printf("free called()\n");

}

/*
 * <what does realloc do?>
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * <what does calloc do?>
 */
void *calloc(size_t elements, size_t size)
{
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    // Multiplication overflowed
    return NULL;

    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * <what does extend_heap do?>
 */
static block_t *extend_heap(size_t size)
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_header(block, size, false);
    write_footer(block, size, false);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);

    // Coalesce in case the previous block was free; also, update the free list
    return coalesce(block);
}

/*
 * <what does coalesce do?>
 */
static block_t *coalesce(block_t * block)
{
    block_t *block_next = find_next(block);
    block_t *block_prev = find_prev(block);

    bool prev_alloc = extract_alloc(*(find_prev_footer(block)));
    bool next_alloc = get_alloc(block_next);
    size_t size = get_size(block);

    if (prev_alloc && next_alloc)              // Case 1, no merging needed
    {
        insert_at_head(block);                 // insert at head, and no more actions.
        //insert_at_tail(block);
        return block;
    }

    else if (prev_alloc && !next_alloc)        // Case 2, next one is free
    {
        size += get_size(block_next);

        // clean up heap
//        write_footer(block, 0, false);      // clear expired footer
//        write_header(block_next, 0, false); // clear expired header


        write_header(block, size, false);
        write_footer(block, size, false);

        // remove block_next from the free block list
        remove_fblk(block_next);


        // insert new free block at the head
        insert_at_head(block);
        //insert_at_tail(block);
    }

    else if (!prev_alloc && next_alloc)        // Case 3, previous one is free
    {
        size += get_size(block_prev);

        // clean up heap
//        write_footer(block_prev, 0, false);      // clear expired footer
//        write_header(block, 0, false); // clear expired header

        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
        block = block_prev;

        // remove block_prev from the free block list
        remove_fblk(block_prev);

        // insert new free block at the head
        insert_at_head(block);
        //insert_at_tail(block);
    }

    else                                        // Case 4, both the previous and the next blocks are free
    {
        size += get_size(block_next) + get_size(block_prev);

        // clean up heap
//        write_footer(block_prev, 0, false);      // clear expired footer
//        write_header(block, 0, false); // clear expired header
//        write_footer(block, 0, false);      // clear expired footer
//        write_header(block_next, 0, false); // clear expired header



        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
        block = block_prev;

        // remove block_prev from the free block list
        remove_fblk(block_prev);

        // remove block_next from the free block list
        remove_fblk(block_next);

        // insert new free block at the head
        insert_at_head(block);
        //insert_at_tail(block);
    }
    return block;
}

/*
 * <what does place do?>
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);

    if ((csize - asize) >= min_block_size)      // enough space to split out another free block
    {
        block_t *block_next;
        write_header(block, asize, true);
        write_footer(block, asize, true);

        block_next = find_next(block);
        write_header(block_next, csize-asize, false);
        write_footer(block_next, csize-asize, false);

        insert_at_head(block_next);
        //insert_at_tail(block_next);
    }

    else
    {
        write_header(block, csize, true);
        write_footer(block, csize, true);

    }

    remove_fblk(block);
}

/*
 * <what does find_fit do?>
 */
static block_t *find_fit(size_t asize)
{
    block_t *fblk;
    fblk = get_head();

    size_t block_size;
    while(fblk!=NULL){
        block_size=get_size(fblk);
        if (asize <= block_size)  //
        {
            return fblk;
        }
        fblk = get_next_fblk(fblk);
    }
    return NULL;
}
/*
 * find_fit_N returns the best fit in the first N
 * free blocks which are larger than asize.
 */
static block_t *find_fit_N(size_t asize,int N){

    block_t *fblk;
    block_t *fblk_bestN = NULL;

    int counter = 0;

    fblk = get_head();

    size_t block_size;
    size_t over_fit = 0;

    while(fblk!=NULL){
        block_size=get_size(fblk);
        if (asize == block_size)  // perfect fit obtained, return immediately.
        {
            return fblk;
        }

        if(block_size>asize){    // found a free block larger than asize
            if(counter==0){
                over_fit = block_size-asize;
                fblk_bestN = fblk;
            }else{
                if(over_fit>block_size-asize){
                    over_fit = block_size-asize;
                    fblk_bestN = fblk;
                }
            }

            // heuristic rule: if a good enough one is found, return;
            if((double)over_fit/(double)asize<0.001) return fblk_bestN;

            counter++;
        }

        if(counter>=N){
            break;
        }
        fblk = get_next_fblk(fblk);

    }
    return fblk_bestN;
}

/*
 * <what does your heap checker do?>
 * Please keep modularity in mind when you're writing the heap checker!
 */
bool mm_checkheap(int line)
{
    unsigned int heap_lo = (unsigned int) mem_heap_lo();
    unsigned int heap_hi = (unsigned int) mem_heap_hi();

    block_t *blockp = heap_start;
    size_t block_size;

    // check prelogue.
    if(extract_size( *((word_t *)blockp-1)) != 0 || extract_alloc( *((word_t *)blockp-1)) == false  ){
        dbg_printf("LINE%d, prologue block 0 error\n",line);
        exit(1);
        return false;
    }

    int counter;
    counter = 0;

    while( (block_size= extract_size(blockp->header))>0 ){

        // ensure that the block point is pointing to the heap
        dbg_assert((unsigned int)blockp<heap_hi && (unsigned int)blockp>= heap_lo);

        word_t block_header = blockp->header;
        word_t *footerp = (word_t *)((blockp->payload) + get_size(blockp) - dsize);
        word_t block_footer = *footerp;

        // check header and footer match
        if(block_header-block_footer){
            dbg_printf("block %d: header does not match footer\n",counter);
            exit(1);
        }
        // check block size, lower bound
        if(block_size<min_block_size){
            dbg_printf("block %d: block size smaller than threshold\n",counter);
            exit(1);
        }
        // check block size, higher bound
        if( (unsigned int) blockp + block_size >=heap_hi){
            dbg_printf("block %d: block size exceeds heap boundary\n",counter);
            exit(1);
        }
        // check block size for alignment.
        if ((word_t) block_size & align_mask){
            dbg_printf("block %d: block size not 16 byte aligned\n",counter);
            exit(1);
        }
        // check block address for alignment.  must be 8 bytes extra with 16 byte alignment
        if ( ((word_t) blockp & align_mask)!=0x8  ){
            dbg_printf("block %d: block address not aligned\n",counter);
            exit(1);
        }
        // check payload address alignment
        if( (word_t) (blockp->payload) & align_mask){
            dbg_printf("block %d: payload address not 16 byte aligned\n",counter);
            exit(1);
        }


        // check for two consecutive free blocks
        bool cur_aloc = get_alloc(blockp);
        if(!cur_aloc){      // current free
            block_t * next_b = find_next(blockp);
            if(next_b){
                if(!get_alloc(next_b)){ //next free
                    dbg_printf("block %d: consecutive free blocks (next)!\n",counter);
                    exit(1);
                }
            }
        }

        counter++;
        block_t * block_next = find_next(blockp);
        if(!block_next){
            break;}
        else{
            blockp = block_next;

        }
    }

    // check epilogue size and allocation
    if(block_size !=0||extract_alloc(blockp->header)==false){
        dbg_printf("epilog error!\n");
        exit(0);
    }

    //dbg_printf("total number of blocks: %d\n",counter);

    (void)heap_lo;
    (void)heap_hi;

    return true;

}

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details within your header comments for the functions above!     *
 *                                                                           *
 *                                                                           *
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a de ad be ef 0a 0a 0a               *
 *                                                                           *
 *****************************************************************************
 */


/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc)
{
    return alloc ? (size | alloc_mask) : size;
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - dsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    block->header = pack(size, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}
