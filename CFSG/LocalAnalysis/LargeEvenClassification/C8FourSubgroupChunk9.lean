module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupValid9
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupKernel9
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRank9

public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk9_valid (j : Fin 64) :
    c8FourRecordValid (c8FourRecordChunk9[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData576_valid
  · exact c8FourRecordData577_valid
  · exact c8FourRecordData578_valid
  · exact c8FourRecordData579_valid
  · exact c8FourRecordData580_valid
  · exact c8FourRecordData581_valid
  · exact c8FourRecordData582_valid
  · exact c8FourRecordData583_valid
  · exact c8FourRecordData584_valid
  · exact c8FourRecordData585_valid
  · exact c8FourRecordData586_valid
  · exact c8FourRecordData587_valid
  · exact c8FourRecordData588_valid
  · exact c8FourRecordData589_valid
  · exact c8FourRecordData590_valid
  · exact c8FourRecordData591_valid
  · exact c8FourRecordData592_valid
  · exact c8FourRecordData593_valid
  · exact c8FourRecordData594_valid
  · exact c8FourRecordData595_valid
  · exact c8FourRecordData596_valid
  · exact c8FourRecordData597_valid
  · exact c8FourRecordData598_valid
  · exact c8FourRecordData599_valid
  · exact c8FourRecordData600_valid
  · exact c8FourRecordData601_valid
  · exact c8FourRecordData602_valid
  · exact c8FourRecordData603_valid
  · exact c8FourRecordData604_valid
  · exact c8FourRecordData605_valid
  · exact c8FourRecordData606_valid
  · exact c8FourRecordData607_valid
  · exact c8FourRecordData608_valid
  · exact c8FourRecordData609_valid
  · exact c8FourRecordData610_valid
  · exact c8FourRecordData611_valid
  · exact c8FourRecordData612_valid
  · exact c8FourRecordData613_valid
  · exact c8FourRecordData614_valid
  · exact c8FourRecordData615_valid
  · exact c8FourRecordData616_valid
  · exact c8FourRecordData617_valid
  · exact c8FourRecordData618_valid
  · exact c8FourRecordData619_valid
  · exact c8FourRecordData620_valid
  · exact c8FourRecordData621_valid
  · exact c8FourRecordData622_valid
  · exact c8FourRecordData623_valid
  · exact c8FourRecordData624_valid
  · exact c8FourRecordData625_valid
  · exact c8FourRecordData626_valid
  · exact c8FourRecordData627_valid
  · exact c8FourRecordData628_valid
  · exact c8FourRecordData629_valid
  · exact c8FourRecordData630_valid
  · exact c8FourRecordData631_valid
  · exact c8FourRecordData632_valid
  · exact c8FourRecordData633_valid
  · exact c8FourRecordData634_valid
  · exact c8FourRecordData635_valid
  · exact c8FourRecordData636_valid
  · exact c8FourRecordData637_valid
  · exact c8FourRecordData638_valid
  · exact c8FourRecordData639_valid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk9_kernels (j : Fin 64) :
    c8FourKernelListsValid (c8FourRecordChunk9[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData576_kernels
  · exact c8FourRecordData577_kernels
  · exact c8FourRecordData578_kernels
  · exact c8FourRecordData579_kernels
  · exact c8FourRecordData580_kernels
  · exact c8FourRecordData581_kernels
  · exact c8FourRecordData582_kernels
  · exact c8FourRecordData583_kernels
  · exact c8FourRecordData584_kernels
  · exact c8FourRecordData585_kernels
  · exact c8FourRecordData586_kernels
  · exact c8FourRecordData587_kernels
  · exact c8FourRecordData588_kernels
  · exact c8FourRecordData589_kernels
  · exact c8FourRecordData590_kernels
  · exact c8FourRecordData591_kernels
  · exact c8FourRecordData592_kernels
  · exact c8FourRecordData593_kernels
  · exact c8FourRecordData594_kernels
  · exact c8FourRecordData595_kernels
  · exact c8FourRecordData596_kernels
  · exact c8FourRecordData597_kernels
  · exact c8FourRecordData598_kernels
  · exact c8FourRecordData599_kernels
  · exact c8FourRecordData600_kernels
  · exact c8FourRecordData601_kernels
  · exact c8FourRecordData602_kernels
  · exact c8FourRecordData603_kernels
  · exact c8FourRecordData604_kernels
  · exact c8FourRecordData605_kernels
  · exact c8FourRecordData606_kernels
  · exact c8FourRecordData607_kernels
  · exact c8FourRecordData608_kernels
  · exact c8FourRecordData609_kernels
  · exact c8FourRecordData610_kernels
  · exact c8FourRecordData611_kernels
  · exact c8FourRecordData612_kernels
  · exact c8FourRecordData613_kernels
  · exact c8FourRecordData614_kernels
  · exact c8FourRecordData615_kernels
  · exact c8FourRecordData616_kernels
  · exact c8FourRecordData617_kernels
  · exact c8FourRecordData618_kernels
  · exact c8FourRecordData619_kernels
  · exact c8FourRecordData620_kernels
  · exact c8FourRecordData621_kernels
  · exact c8FourRecordData622_kernels
  · exact c8FourRecordData623_kernels
  · exact c8FourRecordData624_kernels
  · exact c8FourRecordData625_kernels
  · exact c8FourRecordData626_kernels
  · exact c8FourRecordData627_kernels
  · exact c8FourRecordData628_kernels
  · exact c8FourRecordData629_kernels
  · exact c8FourRecordData630_kernels
  · exact c8FourRecordData631_kernels
  · exact c8FourRecordData632_kernels
  · exact c8FourRecordData633_kernels
  · exact c8FourRecordData634_kernels
  · exact c8FourRecordData635_kernels
  · exact c8FourRecordData636_kernels
  · exact c8FourRecordData637_kernels
  · exact c8FourRecordData638_kernels
  · exact c8FourRecordData639_kernels

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk9_vectors (j : Fin 64) :
    c8FourGeneratorVectorsValid (c8FourRecordChunk9[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData576_vectors
  · exact c8FourRecordData577_vectors
  · exact c8FourRecordData578_vectors
  · exact c8FourRecordData579_vectors
  · exact c8FourRecordData580_vectors
  · exact c8FourRecordData581_vectors
  · exact c8FourRecordData582_vectors
  · exact c8FourRecordData583_vectors
  · exact c8FourRecordData584_vectors
  · exact c8FourRecordData585_vectors
  · exact c8FourRecordData586_vectors
  · exact c8FourRecordData587_vectors
  · exact c8FourRecordData588_vectors
  · exact c8FourRecordData589_vectors
  · exact c8FourRecordData590_vectors
  · exact c8FourRecordData591_vectors
  · exact c8FourRecordData592_vectors
  · exact c8FourRecordData593_vectors
  · exact c8FourRecordData594_vectors
  · exact c8FourRecordData595_vectors
  · exact c8FourRecordData596_vectors
  · exact c8FourRecordData597_vectors
  · exact c8FourRecordData598_vectors
  · exact c8FourRecordData599_vectors
  · exact c8FourRecordData600_vectors
  · exact c8FourRecordData601_vectors
  · exact c8FourRecordData602_vectors
  · exact c8FourRecordData603_vectors
  · exact c8FourRecordData604_vectors
  · exact c8FourRecordData605_vectors
  · exact c8FourRecordData606_vectors
  · exact c8FourRecordData607_vectors
  · exact c8FourRecordData608_vectors
  · exact c8FourRecordData609_vectors
  · exact c8FourRecordData610_vectors
  · exact c8FourRecordData611_vectors
  · exact c8FourRecordData612_vectors
  · exact c8FourRecordData613_vectors
  · exact c8FourRecordData614_vectors
  · exact c8FourRecordData615_vectors
  · exact c8FourRecordData616_vectors
  · exact c8FourRecordData617_vectors
  · exact c8FourRecordData618_vectors
  · exact c8FourRecordData619_vectors
  · exact c8FourRecordData620_vectors
  · exact c8FourRecordData621_vectors
  · exact c8FourRecordData622_vectors
  · exact c8FourRecordData623_vectors
  · exact c8FourRecordData624_vectors
  · exact c8FourRecordData625_vectors
  · exact c8FourRecordData626_vectors
  · exact c8FourRecordData627_vectors
  · exact c8FourRecordData628_vectors
  · exact c8FourRecordData629_vectors
  · exact c8FourRecordData630_vectors
  · exact c8FourRecordData631_vectors
  · exact c8FourRecordData632_vectors
  · exact c8FourRecordData633_vectors
  · exact c8FourRecordData634_vectors
  · exact c8FourRecordData635_vectors
  · exact c8FourRecordData636_vectors
  · exact c8FourRecordData637_vectors
  · exact c8FourRecordData638_vectors
  · exact c8FourRecordData639_vectors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk9_rank_cards (j : Fin 64) :
    (c8FourRecordBinaryImages (c8FourRecordChunk9[j.val]!)).card = 2 ^ (c8FourRecordChunk9[j.val]!).generators.length := by
  fin_cases j
  · change (c8FourRecordBinaryImages c8FourRecordData576).card = 2 ^ c8FourRecordData576.generators.length
    rw [(c8FourRecordData576_rank_card).2]
    exact (c8FourRecordData576_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData577).card = 2 ^ c8FourRecordData577.generators.length
    rw [(c8FourRecordData577_rank_card).2]
    exact (c8FourRecordData577_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData578).card = 2 ^ c8FourRecordData578.generators.length
    rw [(c8FourRecordData578_rank_card).2]
    exact (c8FourRecordData578_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData579).card = 2 ^ c8FourRecordData579.generators.length
    rw [(c8FourRecordData579_rank_card).2]
    exact (c8FourRecordData579_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData580).card = 2 ^ c8FourRecordData580.generators.length
    rw [(c8FourRecordData580_rank_card).2]
    exact (c8FourRecordData580_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData581).card = 2 ^ c8FourRecordData581.generators.length
    rw [(c8FourRecordData581_rank_card).2]
    exact (c8FourRecordData581_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData582).card = 2 ^ c8FourRecordData582.generators.length
    rw [(c8FourRecordData582_rank_card).2]
    exact (c8FourRecordData582_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData583).card = 2 ^ c8FourRecordData583.generators.length
    rw [(c8FourRecordData583_rank_card).2]
    exact (c8FourRecordData583_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData584).card = 2 ^ c8FourRecordData584.generators.length
    rw [(c8FourRecordData584_rank_card).2]
    exact (c8FourRecordData584_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData585).card = 2 ^ c8FourRecordData585.generators.length
    rw [(c8FourRecordData585_rank_card).2]
    exact (c8FourRecordData585_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData586).card = 2 ^ c8FourRecordData586.generators.length
    rw [(c8FourRecordData586_rank_card).2]
    exact (c8FourRecordData586_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData587).card = 2 ^ c8FourRecordData587.generators.length
    rw [(c8FourRecordData587_rank_card).2]
    exact (c8FourRecordData587_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData588).card = 2 ^ c8FourRecordData588.generators.length
    rw [(c8FourRecordData588_rank_card).2]
    exact (c8FourRecordData588_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData589).card = 2 ^ c8FourRecordData589.generators.length
    rw [(c8FourRecordData589_rank_card).2]
    exact (c8FourRecordData589_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData590).card = 2 ^ c8FourRecordData590.generators.length
    rw [(c8FourRecordData590_rank_card).2]
    exact (c8FourRecordData590_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData591).card = 2 ^ c8FourRecordData591.generators.length
    rw [(c8FourRecordData591_rank_card).2]
    exact (c8FourRecordData591_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData592).card = 2 ^ c8FourRecordData592.generators.length
    rw [(c8FourRecordData592_rank_card).2]
    exact (c8FourRecordData592_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData593).card = 2 ^ c8FourRecordData593.generators.length
    rw [(c8FourRecordData593_rank_card).2]
    exact (c8FourRecordData593_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData594).card = 2 ^ c8FourRecordData594.generators.length
    rw [(c8FourRecordData594_rank_card).2]
    exact (c8FourRecordData594_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData595).card = 2 ^ c8FourRecordData595.generators.length
    rw [(c8FourRecordData595_rank_card).2]
    exact (c8FourRecordData595_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData596).card = 2 ^ c8FourRecordData596.generators.length
    rw [(c8FourRecordData596_rank_card).2]
    exact (c8FourRecordData596_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData597).card = 2 ^ c8FourRecordData597.generators.length
    rw [(c8FourRecordData597_rank_card).2]
    exact (c8FourRecordData597_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData598).card = 2 ^ c8FourRecordData598.generators.length
    rw [(c8FourRecordData598_rank_card).2]
    exact (c8FourRecordData598_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData599).card = 2 ^ c8FourRecordData599.generators.length
    rw [(c8FourRecordData599_rank_card).2]
    exact (c8FourRecordData599_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData600).card = 2 ^ c8FourRecordData600.generators.length
    rw [(c8FourRecordData600_rank_card).2]
    exact (c8FourRecordData600_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData601).card = 2 ^ c8FourRecordData601.generators.length
    rw [(c8FourRecordData601_rank_card).2]
    exact (c8FourRecordData601_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData602).card = 2 ^ c8FourRecordData602.generators.length
    rw [(c8FourRecordData602_rank_card).2]
    exact (c8FourRecordData602_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData603).card = 2 ^ c8FourRecordData603.generators.length
    rw [(c8FourRecordData603_rank_card).2]
    exact (c8FourRecordData603_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData604).card = 2 ^ c8FourRecordData604.generators.length
    rw [(c8FourRecordData604_rank_card).2]
    exact (c8FourRecordData604_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData605).card = 2 ^ c8FourRecordData605.generators.length
    rw [(c8FourRecordData605_rank_card).2]
    exact (c8FourRecordData605_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData606).card = 2 ^ c8FourRecordData606.generators.length
    rw [(c8FourRecordData606_rank_card).2]
    exact (c8FourRecordData606_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData607).card = 2 ^ c8FourRecordData607.generators.length
    rw [(c8FourRecordData607_rank_card).2]
    exact (c8FourRecordData607_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData608).card = 2 ^ c8FourRecordData608.generators.length
    rw [(c8FourRecordData608_rank_card).2]
    exact (c8FourRecordData608_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData609).card = 2 ^ c8FourRecordData609.generators.length
    rw [(c8FourRecordData609_rank_card).2]
    exact (c8FourRecordData609_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData610).card = 2 ^ c8FourRecordData610.generators.length
    rw [(c8FourRecordData610_rank_card).2]
    exact (c8FourRecordData610_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData611).card = 2 ^ c8FourRecordData611.generators.length
    rw [(c8FourRecordData611_rank_card).2]
    exact (c8FourRecordData611_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData612).card = 2 ^ c8FourRecordData612.generators.length
    rw [(c8FourRecordData612_rank_card).2]
    exact (c8FourRecordData612_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData613).card = 2 ^ c8FourRecordData613.generators.length
    rw [(c8FourRecordData613_rank_card).2]
    exact (c8FourRecordData613_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData614).card = 2 ^ c8FourRecordData614.generators.length
    rw [(c8FourRecordData614_rank_card).2]
    exact (c8FourRecordData614_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData615).card = 2 ^ c8FourRecordData615.generators.length
    rw [(c8FourRecordData615_rank_card).2]
    exact (c8FourRecordData615_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData616).card = 2 ^ c8FourRecordData616.generators.length
    rw [(c8FourRecordData616_rank_card).2]
    exact (c8FourRecordData616_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData617).card = 2 ^ c8FourRecordData617.generators.length
    rw [(c8FourRecordData617_rank_card).2]
    exact (c8FourRecordData617_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData618).card = 2 ^ c8FourRecordData618.generators.length
    rw [(c8FourRecordData618_rank_card).2]
    exact (c8FourRecordData618_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData619).card = 2 ^ c8FourRecordData619.generators.length
    rw [(c8FourRecordData619_rank_card).2]
    exact (c8FourRecordData619_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData620).card = 2 ^ c8FourRecordData620.generators.length
    rw [(c8FourRecordData620_rank_card).2]
    exact (c8FourRecordData620_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData621).card = 2 ^ c8FourRecordData621.generators.length
    rw [(c8FourRecordData621_rank_card).2]
    exact (c8FourRecordData621_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData622).card = 2 ^ c8FourRecordData622.generators.length
    rw [(c8FourRecordData622_rank_card).2]
    exact (c8FourRecordData622_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData623).card = 2 ^ c8FourRecordData623.generators.length
    rw [(c8FourRecordData623_rank_card).2]
    exact (c8FourRecordData623_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData624).card = 2 ^ c8FourRecordData624.generators.length
    rw [(c8FourRecordData624_rank_card).2]
    exact (c8FourRecordData624_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData625).card = 2 ^ c8FourRecordData625.generators.length
    rw [(c8FourRecordData625_rank_card).2]
    exact (c8FourRecordData625_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData626).card = 2 ^ c8FourRecordData626.generators.length
    rw [(c8FourRecordData626_rank_card).2]
    exact (c8FourRecordData626_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData627).card = 2 ^ c8FourRecordData627.generators.length
    rw [(c8FourRecordData627_rank_card).2]
    exact (c8FourRecordData627_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData628).card = 2 ^ c8FourRecordData628.generators.length
    rw [(c8FourRecordData628_rank_card).2]
    exact (c8FourRecordData628_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData629).card = 2 ^ c8FourRecordData629.generators.length
    rw [(c8FourRecordData629_rank_card).2]
    exact (c8FourRecordData629_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData630).card = 2 ^ c8FourRecordData630.generators.length
    rw [(c8FourRecordData630_rank_card).2]
    exact (c8FourRecordData630_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData631).card = 2 ^ c8FourRecordData631.generators.length
    rw [(c8FourRecordData631_rank_card).2]
    exact (c8FourRecordData631_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData632).card = 2 ^ c8FourRecordData632.generators.length
    rw [(c8FourRecordData632_rank_card).2]
    exact (c8FourRecordData632_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData633).card = 2 ^ c8FourRecordData633.generators.length
    rw [(c8FourRecordData633_rank_card).2]
    exact (c8FourRecordData633_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData634).card = 2 ^ c8FourRecordData634.generators.length
    rw [(c8FourRecordData634_rank_card).2]
    exact (c8FourRecordData634_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData635).card = 2 ^ c8FourRecordData635.generators.length
    rw [(c8FourRecordData635_rank_card).2]
    exact (c8FourRecordData635_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData636).card = 2 ^ c8FourRecordData636.generators.length
    rw [(c8FourRecordData636_rank_card).2]
    exact (c8FourRecordData636_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData637).card = 2 ^ c8FourRecordData637.generators.length
    rw [(c8FourRecordData637_rank_card).2]
    exact (c8FourRecordData637_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData638).card = 2 ^ c8FourRecordData638.generators.length
    rw [(c8FourRecordData638_rank_card).2]
    exact (c8FourRecordData638_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData639).card = 2 ^ c8FourRecordData639.generators.length
    rw [(c8FourRecordData639_rank_card).2]
    exact (c8FourRecordData639_rank_card).1

end CFSG.LargeEvenClassification.Helpers
