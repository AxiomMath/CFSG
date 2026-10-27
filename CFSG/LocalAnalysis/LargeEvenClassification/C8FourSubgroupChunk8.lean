module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupValid8
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupKernel8
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRank8

public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk8_valid (j : Fin 64) :
    c8FourRecordValid (c8FourRecordChunk8[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData512_valid
  · exact c8FourRecordData513_valid
  · exact c8FourRecordData514_valid
  · exact c8FourRecordData515_valid
  · exact c8FourRecordData516_valid
  · exact c8FourRecordData517_valid
  · exact c8FourRecordData518_valid
  · exact c8FourRecordData519_valid
  · exact c8FourRecordData520_valid
  · exact c8FourRecordData521_valid
  · exact c8FourRecordData522_valid
  · exact c8FourRecordData523_valid
  · exact c8FourRecordData524_valid
  · exact c8FourRecordData525_valid
  · exact c8FourRecordData526_valid
  · exact c8FourRecordData527_valid
  · exact c8FourRecordData528_valid
  · exact c8FourRecordData529_valid
  · exact c8FourRecordData530_valid
  · exact c8FourRecordData531_valid
  · exact c8FourRecordData532_valid
  · exact c8FourRecordData533_valid
  · exact c8FourRecordData534_valid
  · exact c8FourRecordData535_valid
  · exact c8FourRecordData536_valid
  · exact c8FourRecordData537_valid
  · exact c8FourRecordData538_valid
  · exact c8FourRecordData539_valid
  · exact c8FourRecordData540_valid
  · exact c8FourRecordData541_valid
  · exact c8FourRecordData542_valid
  · exact c8FourRecordData543_valid
  · exact c8FourRecordData544_valid
  · exact c8FourRecordData545_valid
  · exact c8FourRecordData546_valid
  · exact c8FourRecordData547_valid
  · exact c8FourRecordData548_valid
  · exact c8FourRecordData549_valid
  · exact c8FourRecordData550_valid
  · exact c8FourRecordData551_valid
  · exact c8FourRecordData552_valid
  · exact c8FourRecordData553_valid
  · exact c8FourRecordData554_valid
  · exact c8FourRecordData555_valid
  · exact c8FourRecordData556_valid
  · exact c8FourRecordData557_valid
  · exact c8FourRecordData558_valid
  · exact c8FourRecordData559_valid
  · exact c8FourRecordData560_valid
  · exact c8FourRecordData561_valid
  · exact c8FourRecordData562_valid
  · exact c8FourRecordData563_valid
  · exact c8FourRecordData564_valid
  · exact c8FourRecordData565_valid
  · exact c8FourRecordData566_valid
  · exact c8FourRecordData567_valid
  · exact c8FourRecordData568_valid
  · exact c8FourRecordData569_valid
  · exact c8FourRecordData570_valid
  · exact c8FourRecordData571_valid
  · exact c8FourRecordData572_valid
  · exact c8FourRecordData573_valid
  · exact c8FourRecordData574_valid
  · exact c8FourRecordData575_valid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk8_kernels (j : Fin 64) :
    c8FourKernelListsValid (c8FourRecordChunk8[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData512_kernels
  · exact c8FourRecordData513_kernels
  · exact c8FourRecordData514_kernels
  · exact c8FourRecordData515_kernels
  · exact c8FourRecordData516_kernels
  · exact c8FourRecordData517_kernels
  · exact c8FourRecordData518_kernels
  · exact c8FourRecordData519_kernels
  · exact c8FourRecordData520_kernels
  · exact c8FourRecordData521_kernels
  · exact c8FourRecordData522_kernels
  · exact c8FourRecordData523_kernels
  · exact c8FourRecordData524_kernels
  · exact c8FourRecordData525_kernels
  · exact c8FourRecordData526_kernels
  · exact c8FourRecordData527_kernels
  · exact c8FourRecordData528_kernels
  · exact c8FourRecordData529_kernels
  · exact c8FourRecordData530_kernels
  · exact c8FourRecordData531_kernels
  · exact c8FourRecordData532_kernels
  · exact c8FourRecordData533_kernels
  · exact c8FourRecordData534_kernels
  · exact c8FourRecordData535_kernels
  · exact c8FourRecordData536_kernels
  · exact c8FourRecordData537_kernels
  · exact c8FourRecordData538_kernels
  · exact c8FourRecordData539_kernels
  · exact c8FourRecordData540_kernels
  · exact c8FourRecordData541_kernels
  · exact c8FourRecordData542_kernels
  · exact c8FourRecordData543_kernels
  · exact c8FourRecordData544_kernels
  · exact c8FourRecordData545_kernels
  · exact c8FourRecordData546_kernels
  · exact c8FourRecordData547_kernels
  · exact c8FourRecordData548_kernels
  · exact c8FourRecordData549_kernels
  · exact c8FourRecordData550_kernels
  · exact c8FourRecordData551_kernels
  · exact c8FourRecordData552_kernels
  · exact c8FourRecordData553_kernels
  · exact c8FourRecordData554_kernels
  · exact c8FourRecordData555_kernels
  · exact c8FourRecordData556_kernels
  · exact c8FourRecordData557_kernels
  · exact c8FourRecordData558_kernels
  · exact c8FourRecordData559_kernels
  · exact c8FourRecordData560_kernels
  · exact c8FourRecordData561_kernels
  · exact c8FourRecordData562_kernels
  · exact c8FourRecordData563_kernels
  · exact c8FourRecordData564_kernels
  · exact c8FourRecordData565_kernels
  · exact c8FourRecordData566_kernels
  · exact c8FourRecordData567_kernels
  · exact c8FourRecordData568_kernels
  · exact c8FourRecordData569_kernels
  · exact c8FourRecordData570_kernels
  · exact c8FourRecordData571_kernels
  · exact c8FourRecordData572_kernels
  · exact c8FourRecordData573_kernels
  · exact c8FourRecordData574_kernels
  · exact c8FourRecordData575_kernels

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk8_vectors (j : Fin 64) :
    c8FourGeneratorVectorsValid (c8FourRecordChunk8[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData512_vectors
  · exact c8FourRecordData513_vectors
  · exact c8FourRecordData514_vectors
  · exact c8FourRecordData515_vectors
  · exact c8FourRecordData516_vectors
  · exact c8FourRecordData517_vectors
  · exact c8FourRecordData518_vectors
  · exact c8FourRecordData519_vectors
  · exact c8FourRecordData520_vectors
  · exact c8FourRecordData521_vectors
  · exact c8FourRecordData522_vectors
  · exact c8FourRecordData523_vectors
  · exact c8FourRecordData524_vectors
  · exact c8FourRecordData525_vectors
  · exact c8FourRecordData526_vectors
  · exact c8FourRecordData527_vectors
  · exact c8FourRecordData528_vectors
  · exact c8FourRecordData529_vectors
  · exact c8FourRecordData530_vectors
  · exact c8FourRecordData531_vectors
  · exact c8FourRecordData532_vectors
  · exact c8FourRecordData533_vectors
  · exact c8FourRecordData534_vectors
  · exact c8FourRecordData535_vectors
  · exact c8FourRecordData536_vectors
  · exact c8FourRecordData537_vectors
  · exact c8FourRecordData538_vectors
  · exact c8FourRecordData539_vectors
  · exact c8FourRecordData540_vectors
  · exact c8FourRecordData541_vectors
  · exact c8FourRecordData542_vectors
  · exact c8FourRecordData543_vectors
  · exact c8FourRecordData544_vectors
  · exact c8FourRecordData545_vectors
  · exact c8FourRecordData546_vectors
  · exact c8FourRecordData547_vectors
  · exact c8FourRecordData548_vectors
  · exact c8FourRecordData549_vectors
  · exact c8FourRecordData550_vectors
  · exact c8FourRecordData551_vectors
  · exact c8FourRecordData552_vectors
  · exact c8FourRecordData553_vectors
  · exact c8FourRecordData554_vectors
  · exact c8FourRecordData555_vectors
  · exact c8FourRecordData556_vectors
  · exact c8FourRecordData557_vectors
  · exact c8FourRecordData558_vectors
  · exact c8FourRecordData559_vectors
  · exact c8FourRecordData560_vectors
  · exact c8FourRecordData561_vectors
  · exact c8FourRecordData562_vectors
  · exact c8FourRecordData563_vectors
  · exact c8FourRecordData564_vectors
  · exact c8FourRecordData565_vectors
  · exact c8FourRecordData566_vectors
  · exact c8FourRecordData567_vectors
  · exact c8FourRecordData568_vectors
  · exact c8FourRecordData569_vectors
  · exact c8FourRecordData570_vectors
  · exact c8FourRecordData571_vectors
  · exact c8FourRecordData572_vectors
  · exact c8FourRecordData573_vectors
  · exact c8FourRecordData574_vectors
  · exact c8FourRecordData575_vectors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk8_rank_cards (j : Fin 64) :
    (c8FourRecordBinaryImages (c8FourRecordChunk8[j.val]!)).card = 2 ^ (c8FourRecordChunk8[j.val]!).generators.length := by
  fin_cases j
  · change (c8FourRecordBinaryImages c8FourRecordData512).card = 2 ^ c8FourRecordData512.generators.length
    rw [(c8FourRecordData512_rank_card).2]
    exact (c8FourRecordData512_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData513).card = 2 ^ c8FourRecordData513.generators.length
    rw [(c8FourRecordData513_rank_card).2]
    exact (c8FourRecordData513_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData514).card = 2 ^ c8FourRecordData514.generators.length
    rw [(c8FourRecordData514_rank_card).2]
    exact (c8FourRecordData514_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData515).card = 2 ^ c8FourRecordData515.generators.length
    rw [(c8FourRecordData515_rank_card).2]
    exact (c8FourRecordData515_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData516).card = 2 ^ c8FourRecordData516.generators.length
    rw [(c8FourRecordData516_rank_card).2]
    exact (c8FourRecordData516_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData517).card = 2 ^ c8FourRecordData517.generators.length
    rw [(c8FourRecordData517_rank_card).2]
    exact (c8FourRecordData517_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData518).card = 2 ^ c8FourRecordData518.generators.length
    rw [(c8FourRecordData518_rank_card).2]
    exact (c8FourRecordData518_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData519).card = 2 ^ c8FourRecordData519.generators.length
    rw [(c8FourRecordData519_rank_card).2]
    exact (c8FourRecordData519_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData520).card = 2 ^ c8FourRecordData520.generators.length
    rw [(c8FourRecordData520_rank_card).2]
    exact (c8FourRecordData520_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData521).card = 2 ^ c8FourRecordData521.generators.length
    rw [(c8FourRecordData521_rank_card).2]
    exact (c8FourRecordData521_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData522).card = 2 ^ c8FourRecordData522.generators.length
    rw [(c8FourRecordData522_rank_card).2]
    exact (c8FourRecordData522_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData523).card = 2 ^ c8FourRecordData523.generators.length
    rw [(c8FourRecordData523_rank_card).2]
    exact (c8FourRecordData523_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData524).card = 2 ^ c8FourRecordData524.generators.length
    rw [(c8FourRecordData524_rank_card).2]
    exact (c8FourRecordData524_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData525).card = 2 ^ c8FourRecordData525.generators.length
    rw [(c8FourRecordData525_rank_card).2]
    exact (c8FourRecordData525_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData526).card = 2 ^ c8FourRecordData526.generators.length
    rw [(c8FourRecordData526_rank_card).2]
    exact (c8FourRecordData526_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData527).card = 2 ^ c8FourRecordData527.generators.length
    rw [(c8FourRecordData527_rank_card).2]
    exact (c8FourRecordData527_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData528).card = 2 ^ c8FourRecordData528.generators.length
    rw [(c8FourRecordData528_rank_card).2]
    exact (c8FourRecordData528_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData529).card = 2 ^ c8FourRecordData529.generators.length
    rw [(c8FourRecordData529_rank_card).2]
    exact (c8FourRecordData529_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData530).card = 2 ^ c8FourRecordData530.generators.length
    rw [(c8FourRecordData530_rank_card).2]
    exact (c8FourRecordData530_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData531).card = 2 ^ c8FourRecordData531.generators.length
    rw [(c8FourRecordData531_rank_card).2]
    exact (c8FourRecordData531_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData532).card = 2 ^ c8FourRecordData532.generators.length
    rw [(c8FourRecordData532_rank_card).2]
    exact (c8FourRecordData532_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData533).card = 2 ^ c8FourRecordData533.generators.length
    rw [(c8FourRecordData533_rank_card).2]
    exact (c8FourRecordData533_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData534).card = 2 ^ c8FourRecordData534.generators.length
    rw [(c8FourRecordData534_rank_card).2]
    exact (c8FourRecordData534_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData535).card = 2 ^ c8FourRecordData535.generators.length
    rw [(c8FourRecordData535_rank_card).2]
    exact (c8FourRecordData535_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData536).card = 2 ^ c8FourRecordData536.generators.length
    rw [(c8FourRecordData536_rank_card).2]
    exact (c8FourRecordData536_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData537).card = 2 ^ c8FourRecordData537.generators.length
    rw [(c8FourRecordData537_rank_card).2]
    exact (c8FourRecordData537_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData538).card = 2 ^ c8FourRecordData538.generators.length
    rw [(c8FourRecordData538_rank_card).2]
    exact (c8FourRecordData538_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData539).card = 2 ^ c8FourRecordData539.generators.length
    rw [(c8FourRecordData539_rank_card).2]
    exact (c8FourRecordData539_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData540).card = 2 ^ c8FourRecordData540.generators.length
    rw [(c8FourRecordData540_rank_card).2]
    exact (c8FourRecordData540_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData541).card = 2 ^ c8FourRecordData541.generators.length
    rw [(c8FourRecordData541_rank_card).2]
    exact (c8FourRecordData541_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData542).card = 2 ^ c8FourRecordData542.generators.length
    rw [(c8FourRecordData542_rank_card).2]
    exact (c8FourRecordData542_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData543).card = 2 ^ c8FourRecordData543.generators.length
    rw [(c8FourRecordData543_rank_card).2]
    exact (c8FourRecordData543_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData544).card = 2 ^ c8FourRecordData544.generators.length
    rw [(c8FourRecordData544_rank_card).2]
    exact (c8FourRecordData544_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData545).card = 2 ^ c8FourRecordData545.generators.length
    rw [(c8FourRecordData545_rank_card).2]
    exact (c8FourRecordData545_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData546).card = 2 ^ c8FourRecordData546.generators.length
    rw [(c8FourRecordData546_rank_card).2]
    exact (c8FourRecordData546_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData547).card = 2 ^ c8FourRecordData547.generators.length
    rw [(c8FourRecordData547_rank_card).2]
    exact (c8FourRecordData547_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData548).card = 2 ^ c8FourRecordData548.generators.length
    rw [(c8FourRecordData548_rank_card).2]
    exact (c8FourRecordData548_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData549).card = 2 ^ c8FourRecordData549.generators.length
    rw [(c8FourRecordData549_rank_card).2]
    exact (c8FourRecordData549_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData550).card = 2 ^ c8FourRecordData550.generators.length
    rw [(c8FourRecordData550_rank_card).2]
    exact (c8FourRecordData550_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData551).card = 2 ^ c8FourRecordData551.generators.length
    rw [(c8FourRecordData551_rank_card).2]
    exact (c8FourRecordData551_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData552).card = 2 ^ c8FourRecordData552.generators.length
    rw [(c8FourRecordData552_rank_card).2]
    exact (c8FourRecordData552_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData553).card = 2 ^ c8FourRecordData553.generators.length
    rw [(c8FourRecordData553_rank_card).2]
    exact (c8FourRecordData553_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData554).card = 2 ^ c8FourRecordData554.generators.length
    rw [(c8FourRecordData554_rank_card).2]
    exact (c8FourRecordData554_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData555).card = 2 ^ c8FourRecordData555.generators.length
    rw [(c8FourRecordData555_rank_card).2]
    exact (c8FourRecordData555_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData556).card = 2 ^ c8FourRecordData556.generators.length
    rw [(c8FourRecordData556_rank_card).2]
    exact (c8FourRecordData556_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData557).card = 2 ^ c8FourRecordData557.generators.length
    rw [(c8FourRecordData557_rank_card).2]
    exact (c8FourRecordData557_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData558).card = 2 ^ c8FourRecordData558.generators.length
    rw [(c8FourRecordData558_rank_card).2]
    exact (c8FourRecordData558_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData559).card = 2 ^ c8FourRecordData559.generators.length
    rw [(c8FourRecordData559_rank_card).2]
    exact (c8FourRecordData559_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData560).card = 2 ^ c8FourRecordData560.generators.length
    rw [(c8FourRecordData560_rank_card).2]
    exact (c8FourRecordData560_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData561).card = 2 ^ c8FourRecordData561.generators.length
    rw [(c8FourRecordData561_rank_card).2]
    exact (c8FourRecordData561_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData562).card = 2 ^ c8FourRecordData562.generators.length
    rw [(c8FourRecordData562_rank_card).2]
    exact (c8FourRecordData562_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData563).card = 2 ^ c8FourRecordData563.generators.length
    rw [(c8FourRecordData563_rank_card).2]
    exact (c8FourRecordData563_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData564).card = 2 ^ c8FourRecordData564.generators.length
    rw [(c8FourRecordData564_rank_card).2]
    exact (c8FourRecordData564_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData565).card = 2 ^ c8FourRecordData565.generators.length
    rw [(c8FourRecordData565_rank_card).2]
    exact (c8FourRecordData565_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData566).card = 2 ^ c8FourRecordData566.generators.length
    rw [(c8FourRecordData566_rank_card).2]
    exact (c8FourRecordData566_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData567).card = 2 ^ c8FourRecordData567.generators.length
    rw [(c8FourRecordData567_rank_card).2]
    exact (c8FourRecordData567_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData568).card = 2 ^ c8FourRecordData568.generators.length
    rw [(c8FourRecordData568_rank_card).2]
    exact (c8FourRecordData568_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData569).card = 2 ^ c8FourRecordData569.generators.length
    rw [(c8FourRecordData569_rank_card).2]
    exact (c8FourRecordData569_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData570).card = 2 ^ c8FourRecordData570.generators.length
    rw [(c8FourRecordData570_rank_card).2]
    exact (c8FourRecordData570_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData571).card = 2 ^ c8FourRecordData571.generators.length
    rw [(c8FourRecordData571_rank_card).2]
    exact (c8FourRecordData571_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData572).card = 2 ^ c8FourRecordData572.generators.length
    rw [(c8FourRecordData572_rank_card).2]
    exact (c8FourRecordData572_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData573).card = 2 ^ c8FourRecordData573.generators.length
    rw [(c8FourRecordData573_rank_card).2]
    exact (c8FourRecordData573_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData574).card = 2 ^ c8FourRecordData574.generators.length
    rw [(c8FourRecordData574_rank_card).2]
    exact (c8FourRecordData574_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData575).card = 2 ^ c8FourRecordData575.generators.length
    rw [(c8FourRecordData575_rank_card).2]
    exact (c8FourRecordData575_rank_card).1

end CFSG.LargeEvenClassification.Helpers
