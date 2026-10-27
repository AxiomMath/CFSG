module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupValid7
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupKernel7
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRank7

public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk7_valid (j : Fin 64) :
    c8FourRecordValid (c8FourRecordChunk7[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData448_valid
  · exact c8FourRecordData449_valid
  · exact c8FourRecordData450_valid
  · exact c8FourRecordData451_valid
  · exact c8FourRecordData452_valid
  · exact c8FourRecordData453_valid
  · exact c8FourRecordData454_valid
  · exact c8FourRecordData455_valid
  · exact c8FourRecordData456_valid
  · exact c8FourRecordData457_valid
  · exact c8FourRecordData458_valid
  · exact c8FourRecordData459_valid
  · exact c8FourRecordData460_valid
  · exact c8FourRecordData461_valid
  · exact c8FourRecordData462_valid
  · exact c8FourRecordData463_valid
  · exact c8FourRecordData464_valid
  · exact c8FourRecordData465_valid
  · exact c8FourRecordData466_valid
  · exact c8FourRecordData467_valid
  · exact c8FourRecordData468_valid
  · exact c8FourRecordData469_valid
  · exact c8FourRecordData470_valid
  · exact c8FourRecordData471_valid
  · exact c8FourRecordData472_valid
  · exact c8FourRecordData473_valid
  · exact c8FourRecordData474_valid
  · exact c8FourRecordData475_valid
  · exact c8FourRecordData476_valid
  · exact c8FourRecordData477_valid
  · exact c8FourRecordData478_valid
  · exact c8FourRecordData479_valid
  · exact c8FourRecordData480_valid
  · exact c8FourRecordData481_valid
  · exact c8FourRecordData482_valid
  · exact c8FourRecordData483_valid
  · exact c8FourRecordData484_valid
  · exact c8FourRecordData485_valid
  · exact c8FourRecordData486_valid
  · exact c8FourRecordData487_valid
  · exact c8FourRecordData488_valid
  · exact c8FourRecordData489_valid
  · exact c8FourRecordData490_valid
  · exact c8FourRecordData491_valid
  · exact c8FourRecordData492_valid
  · exact c8FourRecordData493_valid
  · exact c8FourRecordData494_valid
  · exact c8FourRecordData495_valid
  · exact c8FourRecordData496_valid
  · exact c8FourRecordData497_valid
  · exact c8FourRecordData498_valid
  · exact c8FourRecordData499_valid
  · exact c8FourRecordData500_valid
  · exact c8FourRecordData501_valid
  · exact c8FourRecordData502_valid
  · exact c8FourRecordData503_valid
  · exact c8FourRecordData504_valid
  · exact c8FourRecordData505_valid
  · exact c8FourRecordData506_valid
  · exact c8FourRecordData507_valid
  · exact c8FourRecordData508_valid
  · exact c8FourRecordData509_valid
  · exact c8FourRecordData510_valid
  · exact c8FourRecordData511_valid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk7_kernels (j : Fin 64) :
    c8FourKernelListsValid (c8FourRecordChunk7[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData448_kernels
  · exact c8FourRecordData449_kernels
  · exact c8FourRecordData450_kernels
  · exact c8FourRecordData451_kernels
  · exact c8FourRecordData452_kernels
  · exact c8FourRecordData453_kernels
  · exact c8FourRecordData454_kernels
  · exact c8FourRecordData455_kernels
  · exact c8FourRecordData456_kernels
  · exact c8FourRecordData457_kernels
  · exact c8FourRecordData458_kernels
  · exact c8FourRecordData459_kernels
  · exact c8FourRecordData460_kernels
  · exact c8FourRecordData461_kernels
  · exact c8FourRecordData462_kernels
  · exact c8FourRecordData463_kernels
  · exact c8FourRecordData464_kernels
  · exact c8FourRecordData465_kernels
  · exact c8FourRecordData466_kernels
  · exact c8FourRecordData467_kernels
  · exact c8FourRecordData468_kernels
  · exact c8FourRecordData469_kernels
  · exact c8FourRecordData470_kernels
  · exact c8FourRecordData471_kernels
  · exact c8FourRecordData472_kernels
  · exact c8FourRecordData473_kernels
  · exact c8FourRecordData474_kernels
  · exact c8FourRecordData475_kernels
  · exact c8FourRecordData476_kernels
  · exact c8FourRecordData477_kernels
  · exact c8FourRecordData478_kernels
  · exact c8FourRecordData479_kernels
  · exact c8FourRecordData480_kernels
  · exact c8FourRecordData481_kernels
  · exact c8FourRecordData482_kernels
  · exact c8FourRecordData483_kernels
  · exact c8FourRecordData484_kernels
  · exact c8FourRecordData485_kernels
  · exact c8FourRecordData486_kernels
  · exact c8FourRecordData487_kernels
  · exact c8FourRecordData488_kernels
  · exact c8FourRecordData489_kernels
  · exact c8FourRecordData490_kernels
  · exact c8FourRecordData491_kernels
  · exact c8FourRecordData492_kernels
  · exact c8FourRecordData493_kernels
  · exact c8FourRecordData494_kernels
  · exact c8FourRecordData495_kernels
  · exact c8FourRecordData496_kernels
  · exact c8FourRecordData497_kernels
  · exact c8FourRecordData498_kernels
  · exact c8FourRecordData499_kernels
  · exact c8FourRecordData500_kernels
  · exact c8FourRecordData501_kernels
  · exact c8FourRecordData502_kernels
  · exact c8FourRecordData503_kernels
  · exact c8FourRecordData504_kernels
  · exact c8FourRecordData505_kernels
  · exact c8FourRecordData506_kernels
  · exact c8FourRecordData507_kernels
  · exact c8FourRecordData508_kernels
  · exact c8FourRecordData509_kernels
  · exact c8FourRecordData510_kernels
  · exact c8FourRecordData511_kernels

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk7_vectors (j : Fin 64) :
    c8FourGeneratorVectorsValid (c8FourRecordChunk7[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData448_vectors
  · exact c8FourRecordData449_vectors
  · exact c8FourRecordData450_vectors
  · exact c8FourRecordData451_vectors
  · exact c8FourRecordData452_vectors
  · exact c8FourRecordData453_vectors
  · exact c8FourRecordData454_vectors
  · exact c8FourRecordData455_vectors
  · exact c8FourRecordData456_vectors
  · exact c8FourRecordData457_vectors
  · exact c8FourRecordData458_vectors
  · exact c8FourRecordData459_vectors
  · exact c8FourRecordData460_vectors
  · exact c8FourRecordData461_vectors
  · exact c8FourRecordData462_vectors
  · exact c8FourRecordData463_vectors
  · exact c8FourRecordData464_vectors
  · exact c8FourRecordData465_vectors
  · exact c8FourRecordData466_vectors
  · exact c8FourRecordData467_vectors
  · exact c8FourRecordData468_vectors
  · exact c8FourRecordData469_vectors
  · exact c8FourRecordData470_vectors
  · exact c8FourRecordData471_vectors
  · exact c8FourRecordData472_vectors
  · exact c8FourRecordData473_vectors
  · exact c8FourRecordData474_vectors
  · exact c8FourRecordData475_vectors
  · exact c8FourRecordData476_vectors
  · exact c8FourRecordData477_vectors
  · exact c8FourRecordData478_vectors
  · exact c8FourRecordData479_vectors
  · exact c8FourRecordData480_vectors
  · exact c8FourRecordData481_vectors
  · exact c8FourRecordData482_vectors
  · exact c8FourRecordData483_vectors
  · exact c8FourRecordData484_vectors
  · exact c8FourRecordData485_vectors
  · exact c8FourRecordData486_vectors
  · exact c8FourRecordData487_vectors
  · exact c8FourRecordData488_vectors
  · exact c8FourRecordData489_vectors
  · exact c8FourRecordData490_vectors
  · exact c8FourRecordData491_vectors
  · exact c8FourRecordData492_vectors
  · exact c8FourRecordData493_vectors
  · exact c8FourRecordData494_vectors
  · exact c8FourRecordData495_vectors
  · exact c8FourRecordData496_vectors
  · exact c8FourRecordData497_vectors
  · exact c8FourRecordData498_vectors
  · exact c8FourRecordData499_vectors
  · exact c8FourRecordData500_vectors
  · exact c8FourRecordData501_vectors
  · exact c8FourRecordData502_vectors
  · exact c8FourRecordData503_vectors
  · exact c8FourRecordData504_vectors
  · exact c8FourRecordData505_vectors
  · exact c8FourRecordData506_vectors
  · exact c8FourRecordData507_vectors
  · exact c8FourRecordData508_vectors
  · exact c8FourRecordData509_vectors
  · exact c8FourRecordData510_vectors
  · exact c8FourRecordData511_vectors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk7_rank_cards (j : Fin 64) :
    (c8FourRecordBinaryImages (c8FourRecordChunk7[j.val]!)).card = 2 ^ (c8FourRecordChunk7[j.val]!).generators.length := by
  fin_cases j
  · change (c8FourRecordBinaryImages c8FourRecordData448).card = 2 ^ c8FourRecordData448.generators.length
    rw [(c8FourRecordData448_rank_card).2]
    exact (c8FourRecordData448_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData449).card = 2 ^ c8FourRecordData449.generators.length
    rw [(c8FourRecordData449_rank_card).2]
    exact (c8FourRecordData449_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData450).card = 2 ^ c8FourRecordData450.generators.length
    rw [(c8FourRecordData450_rank_card).2]
    exact (c8FourRecordData450_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData451).card = 2 ^ c8FourRecordData451.generators.length
    rw [(c8FourRecordData451_rank_card).2]
    exact (c8FourRecordData451_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData452).card = 2 ^ c8FourRecordData452.generators.length
    rw [(c8FourRecordData452_rank_card).2]
    exact (c8FourRecordData452_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData453).card = 2 ^ c8FourRecordData453.generators.length
    rw [(c8FourRecordData453_rank_card).2]
    exact (c8FourRecordData453_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData454).card = 2 ^ c8FourRecordData454.generators.length
    rw [(c8FourRecordData454_rank_card).2]
    exact (c8FourRecordData454_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData455).card = 2 ^ c8FourRecordData455.generators.length
    rw [(c8FourRecordData455_rank_card).2]
    exact (c8FourRecordData455_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData456).card = 2 ^ c8FourRecordData456.generators.length
    rw [(c8FourRecordData456_rank_card).2]
    exact (c8FourRecordData456_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData457).card = 2 ^ c8FourRecordData457.generators.length
    rw [(c8FourRecordData457_rank_card).2]
    exact (c8FourRecordData457_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData458).card = 2 ^ c8FourRecordData458.generators.length
    rw [(c8FourRecordData458_rank_card).2]
    exact (c8FourRecordData458_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData459).card = 2 ^ c8FourRecordData459.generators.length
    rw [(c8FourRecordData459_rank_card).2]
    exact (c8FourRecordData459_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData460).card = 2 ^ c8FourRecordData460.generators.length
    rw [(c8FourRecordData460_rank_card).2]
    exact (c8FourRecordData460_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData461).card = 2 ^ c8FourRecordData461.generators.length
    rw [(c8FourRecordData461_rank_card).2]
    exact (c8FourRecordData461_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData462).card = 2 ^ c8FourRecordData462.generators.length
    rw [(c8FourRecordData462_rank_card).2]
    exact (c8FourRecordData462_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData463).card = 2 ^ c8FourRecordData463.generators.length
    rw [(c8FourRecordData463_rank_card).2]
    exact (c8FourRecordData463_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData464).card = 2 ^ c8FourRecordData464.generators.length
    rw [(c8FourRecordData464_rank_card).2]
    exact (c8FourRecordData464_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData465).card = 2 ^ c8FourRecordData465.generators.length
    rw [(c8FourRecordData465_rank_card).2]
    exact (c8FourRecordData465_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData466).card = 2 ^ c8FourRecordData466.generators.length
    rw [(c8FourRecordData466_rank_card).2]
    exact (c8FourRecordData466_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData467).card = 2 ^ c8FourRecordData467.generators.length
    rw [(c8FourRecordData467_rank_card).2]
    exact (c8FourRecordData467_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData468).card = 2 ^ c8FourRecordData468.generators.length
    rw [(c8FourRecordData468_rank_card).2]
    exact (c8FourRecordData468_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData469).card = 2 ^ c8FourRecordData469.generators.length
    rw [(c8FourRecordData469_rank_card).2]
    exact (c8FourRecordData469_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData470).card = 2 ^ c8FourRecordData470.generators.length
    rw [(c8FourRecordData470_rank_card).2]
    exact (c8FourRecordData470_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData471).card = 2 ^ c8FourRecordData471.generators.length
    rw [(c8FourRecordData471_rank_card).2]
    exact (c8FourRecordData471_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData472).card = 2 ^ c8FourRecordData472.generators.length
    rw [(c8FourRecordData472_rank_card).2]
    exact (c8FourRecordData472_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData473).card = 2 ^ c8FourRecordData473.generators.length
    rw [(c8FourRecordData473_rank_card).2]
    exact (c8FourRecordData473_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData474).card = 2 ^ c8FourRecordData474.generators.length
    rw [(c8FourRecordData474_rank_card).2]
    exact (c8FourRecordData474_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData475).card = 2 ^ c8FourRecordData475.generators.length
    rw [(c8FourRecordData475_rank_card).2]
    exact (c8FourRecordData475_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData476).card = 2 ^ c8FourRecordData476.generators.length
    rw [(c8FourRecordData476_rank_card).2]
    exact (c8FourRecordData476_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData477).card = 2 ^ c8FourRecordData477.generators.length
    rw [(c8FourRecordData477_rank_card).2]
    exact (c8FourRecordData477_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData478).card = 2 ^ c8FourRecordData478.generators.length
    rw [(c8FourRecordData478_rank_card).2]
    exact (c8FourRecordData478_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData479).card = 2 ^ c8FourRecordData479.generators.length
    rw [(c8FourRecordData479_rank_card).2]
    exact (c8FourRecordData479_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData480).card = 2 ^ c8FourRecordData480.generators.length
    rw [(c8FourRecordData480_rank_card).2]
    exact (c8FourRecordData480_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData481).card = 2 ^ c8FourRecordData481.generators.length
    rw [(c8FourRecordData481_rank_card).2]
    exact (c8FourRecordData481_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData482).card = 2 ^ c8FourRecordData482.generators.length
    rw [(c8FourRecordData482_rank_card).2]
    exact (c8FourRecordData482_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData483).card = 2 ^ c8FourRecordData483.generators.length
    rw [(c8FourRecordData483_rank_card).2]
    exact (c8FourRecordData483_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData484).card = 2 ^ c8FourRecordData484.generators.length
    rw [(c8FourRecordData484_rank_card).2]
    exact (c8FourRecordData484_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData485).card = 2 ^ c8FourRecordData485.generators.length
    rw [(c8FourRecordData485_rank_card).2]
    exact (c8FourRecordData485_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData486).card = 2 ^ c8FourRecordData486.generators.length
    rw [(c8FourRecordData486_rank_card).2]
    exact (c8FourRecordData486_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData487).card = 2 ^ c8FourRecordData487.generators.length
    rw [(c8FourRecordData487_rank_card).2]
    exact (c8FourRecordData487_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData488).card = 2 ^ c8FourRecordData488.generators.length
    rw [(c8FourRecordData488_rank_card).2]
    exact (c8FourRecordData488_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData489).card = 2 ^ c8FourRecordData489.generators.length
    rw [(c8FourRecordData489_rank_card).2]
    exact (c8FourRecordData489_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData490).card = 2 ^ c8FourRecordData490.generators.length
    rw [(c8FourRecordData490_rank_card).2]
    exact (c8FourRecordData490_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData491).card = 2 ^ c8FourRecordData491.generators.length
    rw [(c8FourRecordData491_rank_card).2]
    exact (c8FourRecordData491_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData492).card = 2 ^ c8FourRecordData492.generators.length
    rw [(c8FourRecordData492_rank_card).2]
    exact (c8FourRecordData492_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData493).card = 2 ^ c8FourRecordData493.generators.length
    rw [(c8FourRecordData493_rank_card).2]
    exact (c8FourRecordData493_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData494).card = 2 ^ c8FourRecordData494.generators.length
    rw [(c8FourRecordData494_rank_card).2]
    exact (c8FourRecordData494_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData495).card = 2 ^ c8FourRecordData495.generators.length
    rw [(c8FourRecordData495_rank_card).2]
    exact (c8FourRecordData495_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData496).card = 2 ^ c8FourRecordData496.generators.length
    rw [(c8FourRecordData496_rank_card).2]
    exact (c8FourRecordData496_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData497).card = 2 ^ c8FourRecordData497.generators.length
    rw [(c8FourRecordData497_rank_card).2]
    exact (c8FourRecordData497_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData498).card = 2 ^ c8FourRecordData498.generators.length
    rw [(c8FourRecordData498_rank_card).2]
    exact (c8FourRecordData498_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData499).card = 2 ^ c8FourRecordData499.generators.length
    rw [(c8FourRecordData499_rank_card).2]
    exact (c8FourRecordData499_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData500).card = 2 ^ c8FourRecordData500.generators.length
    rw [(c8FourRecordData500_rank_card).2]
    exact (c8FourRecordData500_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData501).card = 2 ^ c8FourRecordData501.generators.length
    rw [(c8FourRecordData501_rank_card).2]
    exact (c8FourRecordData501_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData502).card = 2 ^ c8FourRecordData502.generators.length
    rw [(c8FourRecordData502_rank_card).2]
    exact (c8FourRecordData502_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData503).card = 2 ^ c8FourRecordData503.generators.length
    rw [(c8FourRecordData503_rank_card).2]
    exact (c8FourRecordData503_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData504).card = 2 ^ c8FourRecordData504.generators.length
    rw [(c8FourRecordData504_rank_card).2]
    exact (c8FourRecordData504_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData505).card = 2 ^ c8FourRecordData505.generators.length
    rw [(c8FourRecordData505_rank_card).2]
    exact (c8FourRecordData505_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData506).card = 2 ^ c8FourRecordData506.generators.length
    rw [(c8FourRecordData506_rank_card).2]
    exact (c8FourRecordData506_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData507).card = 2 ^ c8FourRecordData507.generators.length
    rw [(c8FourRecordData507_rank_card).2]
    exact (c8FourRecordData507_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData508).card = 2 ^ c8FourRecordData508.generators.length
    rw [(c8FourRecordData508_rank_card).2]
    exact (c8FourRecordData508_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData509).card = 2 ^ c8FourRecordData509.generators.length
    rw [(c8FourRecordData509_rank_card).2]
    exact (c8FourRecordData509_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData510).card = 2 ^ c8FourRecordData510.generators.length
    rw [(c8FourRecordData510_rank_card).2]
    exact (c8FourRecordData510_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData511).card = 2 ^ c8FourRecordData511.generators.length
    rw [(c8FourRecordData511_rank_card).2]
    exact (c8FourRecordData511_rank_card).1

end CFSG.LargeEvenClassification.Helpers
