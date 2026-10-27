module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupValid10
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupKernel10
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRank10

public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk10_valid (j : Fin 64) :
    c8FourRecordValid (c8FourRecordChunk10[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData640_valid
  · exact c8FourRecordData641_valid
  · exact c8FourRecordData642_valid
  · exact c8FourRecordData643_valid
  · exact c8FourRecordData644_valid
  · exact c8FourRecordData645_valid
  · exact c8FourRecordData646_valid
  · exact c8FourRecordData647_valid
  · exact c8FourRecordData648_valid
  · exact c8FourRecordData649_valid
  · exact c8FourRecordData650_valid
  · exact c8FourRecordData651_valid
  · exact c8FourRecordData652_valid
  · exact c8FourRecordData653_valid
  · exact c8FourRecordData654_valid
  · exact c8FourRecordData655_valid
  · exact c8FourRecordData656_valid
  · exact c8FourRecordData657_valid
  · exact c8FourRecordData658_valid
  · exact c8FourRecordData659_valid
  · exact c8FourRecordData660_valid
  · exact c8FourRecordData661_valid
  · exact c8FourRecordData662_valid
  · exact c8FourRecordData663_valid
  · exact c8FourRecordData664_valid
  · exact c8FourRecordData665_valid
  · exact c8FourRecordData666_valid
  · exact c8FourRecordData667_valid
  · exact c8FourRecordData668_valid
  · exact c8FourRecordData669_valid
  · exact c8FourRecordData670_valid
  · exact c8FourRecordData671_valid
  · exact c8FourRecordData672_valid
  · exact c8FourRecordData673_valid
  · exact c8FourRecordData674_valid
  · exact c8FourRecordData675_valid
  · exact c8FourRecordData676_valid
  · exact c8FourRecordData677_valid
  · exact c8FourRecordData678_valid
  · exact c8FourRecordData679_valid
  · exact c8FourRecordData680_valid
  · exact c8FourRecordData681_valid
  · exact c8FourRecordData682_valid
  · exact c8FourRecordData683_valid
  · exact c8FourRecordData684_valid
  · exact c8FourRecordData685_valid
  · exact c8FourRecordData686_valid
  · exact c8FourRecordData687_valid
  · exact c8FourRecordData688_valid
  · exact c8FourRecordData689_valid
  · exact c8FourRecordData690_valid
  · exact c8FourRecordData691_valid
  · exact c8FourRecordData692_valid
  · exact c8FourRecordData693_valid
  · exact c8FourRecordData694_valid
  · exact c8FourRecordData695_valid
  · exact c8FourRecordData696_valid
  · exact c8FourRecordData697_valid
  · exact c8FourRecordData698_valid
  · exact c8FourRecordData699_valid
  · exact c8FourRecordData700_valid
  · exact c8FourRecordData701_valid
  · exact c8FourRecordData702_valid
  · exact c8FourRecordData703_valid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk10_kernels (j : Fin 64) :
    c8FourKernelListsValid (c8FourRecordChunk10[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData640_kernels
  · exact c8FourRecordData641_kernels
  · exact c8FourRecordData642_kernels
  · exact c8FourRecordData643_kernels
  · exact c8FourRecordData644_kernels
  · exact c8FourRecordData645_kernels
  · exact c8FourRecordData646_kernels
  · exact c8FourRecordData647_kernels
  · exact c8FourRecordData648_kernels
  · exact c8FourRecordData649_kernels
  · exact c8FourRecordData650_kernels
  · exact c8FourRecordData651_kernels
  · exact c8FourRecordData652_kernels
  · exact c8FourRecordData653_kernels
  · exact c8FourRecordData654_kernels
  · exact c8FourRecordData655_kernels
  · exact c8FourRecordData656_kernels
  · exact c8FourRecordData657_kernels
  · exact c8FourRecordData658_kernels
  · exact c8FourRecordData659_kernels
  · exact c8FourRecordData660_kernels
  · exact c8FourRecordData661_kernels
  · exact c8FourRecordData662_kernels
  · exact c8FourRecordData663_kernels
  · exact c8FourRecordData664_kernels
  · exact c8FourRecordData665_kernels
  · exact c8FourRecordData666_kernels
  · exact c8FourRecordData667_kernels
  · exact c8FourRecordData668_kernels
  · exact c8FourRecordData669_kernels
  · exact c8FourRecordData670_kernels
  · exact c8FourRecordData671_kernels
  · exact c8FourRecordData672_kernels
  · exact c8FourRecordData673_kernels
  · exact c8FourRecordData674_kernels
  · exact c8FourRecordData675_kernels
  · exact c8FourRecordData676_kernels
  · exact c8FourRecordData677_kernels
  · exact c8FourRecordData678_kernels
  · exact c8FourRecordData679_kernels
  · exact c8FourRecordData680_kernels
  · exact c8FourRecordData681_kernels
  · exact c8FourRecordData682_kernels
  · exact c8FourRecordData683_kernels
  · exact c8FourRecordData684_kernels
  · exact c8FourRecordData685_kernels
  · exact c8FourRecordData686_kernels
  · exact c8FourRecordData687_kernels
  · exact c8FourRecordData688_kernels
  · exact c8FourRecordData689_kernels
  · exact c8FourRecordData690_kernels
  · exact c8FourRecordData691_kernels
  · exact c8FourRecordData692_kernels
  · exact c8FourRecordData693_kernels
  · exact c8FourRecordData694_kernels
  · exact c8FourRecordData695_kernels
  · exact c8FourRecordData696_kernels
  · exact c8FourRecordData697_kernels
  · exact c8FourRecordData698_kernels
  · exact c8FourRecordData699_kernels
  · exact c8FourRecordData700_kernels
  · exact c8FourRecordData701_kernels
  · exact c8FourRecordData702_kernels
  · exact c8FourRecordData703_kernels

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk10_vectors (j : Fin 64) :
    c8FourGeneratorVectorsValid (c8FourRecordChunk10[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData640_vectors
  · exact c8FourRecordData641_vectors
  · exact c8FourRecordData642_vectors
  · exact c8FourRecordData643_vectors
  · exact c8FourRecordData644_vectors
  · exact c8FourRecordData645_vectors
  · exact c8FourRecordData646_vectors
  · exact c8FourRecordData647_vectors
  · exact c8FourRecordData648_vectors
  · exact c8FourRecordData649_vectors
  · exact c8FourRecordData650_vectors
  · exact c8FourRecordData651_vectors
  · exact c8FourRecordData652_vectors
  · exact c8FourRecordData653_vectors
  · exact c8FourRecordData654_vectors
  · exact c8FourRecordData655_vectors
  · exact c8FourRecordData656_vectors
  · exact c8FourRecordData657_vectors
  · exact c8FourRecordData658_vectors
  · exact c8FourRecordData659_vectors
  · exact c8FourRecordData660_vectors
  · exact c8FourRecordData661_vectors
  · exact c8FourRecordData662_vectors
  · exact c8FourRecordData663_vectors
  · exact c8FourRecordData664_vectors
  · exact c8FourRecordData665_vectors
  · exact c8FourRecordData666_vectors
  · exact c8FourRecordData667_vectors
  · exact c8FourRecordData668_vectors
  · exact c8FourRecordData669_vectors
  · exact c8FourRecordData670_vectors
  · exact c8FourRecordData671_vectors
  · exact c8FourRecordData672_vectors
  · exact c8FourRecordData673_vectors
  · exact c8FourRecordData674_vectors
  · exact c8FourRecordData675_vectors
  · exact c8FourRecordData676_vectors
  · exact c8FourRecordData677_vectors
  · exact c8FourRecordData678_vectors
  · exact c8FourRecordData679_vectors
  · exact c8FourRecordData680_vectors
  · exact c8FourRecordData681_vectors
  · exact c8FourRecordData682_vectors
  · exact c8FourRecordData683_vectors
  · exact c8FourRecordData684_vectors
  · exact c8FourRecordData685_vectors
  · exact c8FourRecordData686_vectors
  · exact c8FourRecordData687_vectors
  · exact c8FourRecordData688_vectors
  · exact c8FourRecordData689_vectors
  · exact c8FourRecordData690_vectors
  · exact c8FourRecordData691_vectors
  · exact c8FourRecordData692_vectors
  · exact c8FourRecordData693_vectors
  · exact c8FourRecordData694_vectors
  · exact c8FourRecordData695_vectors
  · exact c8FourRecordData696_vectors
  · exact c8FourRecordData697_vectors
  · exact c8FourRecordData698_vectors
  · exact c8FourRecordData699_vectors
  · exact c8FourRecordData700_vectors
  · exact c8FourRecordData701_vectors
  · exact c8FourRecordData702_vectors
  · exact c8FourRecordData703_vectors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk10_rank_cards (j : Fin 64) :
    (c8FourRecordBinaryImages (c8FourRecordChunk10[j.val]!)).card = 2 ^ (c8FourRecordChunk10[j.val]!).generators.length := by
  fin_cases j
  · change (c8FourRecordBinaryImages c8FourRecordData640).card = 2 ^ c8FourRecordData640.generators.length
    rw [(c8FourRecordData640_rank_card).2]
    exact (c8FourRecordData640_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData641).card = 2 ^ c8FourRecordData641.generators.length
    rw [(c8FourRecordData641_rank_card).2]
    exact (c8FourRecordData641_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData642).card = 2 ^ c8FourRecordData642.generators.length
    rw [(c8FourRecordData642_rank_card).2]
    exact (c8FourRecordData642_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData643).card = 2 ^ c8FourRecordData643.generators.length
    rw [(c8FourRecordData643_rank_card).2]
    exact (c8FourRecordData643_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData644).card = 2 ^ c8FourRecordData644.generators.length
    rw [(c8FourRecordData644_rank_card).2]
    exact (c8FourRecordData644_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData645).card = 2 ^ c8FourRecordData645.generators.length
    rw [(c8FourRecordData645_rank_card).2]
    exact (c8FourRecordData645_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData646).card = 2 ^ c8FourRecordData646.generators.length
    rw [(c8FourRecordData646_rank_card).2]
    exact (c8FourRecordData646_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData647).card = 2 ^ c8FourRecordData647.generators.length
    rw [(c8FourRecordData647_rank_card).2]
    exact (c8FourRecordData647_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData648).card = 2 ^ c8FourRecordData648.generators.length
    rw [(c8FourRecordData648_rank_card).2]
    exact (c8FourRecordData648_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData649).card = 2 ^ c8FourRecordData649.generators.length
    rw [(c8FourRecordData649_rank_card).2]
    exact (c8FourRecordData649_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData650).card = 2 ^ c8FourRecordData650.generators.length
    rw [(c8FourRecordData650_rank_card).2]
    exact (c8FourRecordData650_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData651).card = 2 ^ c8FourRecordData651.generators.length
    rw [(c8FourRecordData651_rank_card).2]
    exact (c8FourRecordData651_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData652).card = 2 ^ c8FourRecordData652.generators.length
    rw [(c8FourRecordData652_rank_card).2]
    exact (c8FourRecordData652_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData653).card = 2 ^ c8FourRecordData653.generators.length
    rw [(c8FourRecordData653_rank_card).2]
    exact (c8FourRecordData653_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData654).card = 2 ^ c8FourRecordData654.generators.length
    rw [(c8FourRecordData654_rank_card).2]
    exact (c8FourRecordData654_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData655).card = 2 ^ c8FourRecordData655.generators.length
    rw [(c8FourRecordData655_rank_card).2]
    exact (c8FourRecordData655_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData656).card = 2 ^ c8FourRecordData656.generators.length
    rw [(c8FourRecordData656_rank_card).2]
    exact (c8FourRecordData656_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData657).card = 2 ^ c8FourRecordData657.generators.length
    rw [(c8FourRecordData657_rank_card).2]
    exact (c8FourRecordData657_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData658).card = 2 ^ c8FourRecordData658.generators.length
    rw [(c8FourRecordData658_rank_card).2]
    exact (c8FourRecordData658_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData659).card = 2 ^ c8FourRecordData659.generators.length
    rw [(c8FourRecordData659_rank_card).2]
    exact (c8FourRecordData659_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData660).card = 2 ^ c8FourRecordData660.generators.length
    rw [(c8FourRecordData660_rank_card).2]
    exact (c8FourRecordData660_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData661).card = 2 ^ c8FourRecordData661.generators.length
    rw [(c8FourRecordData661_rank_card).2]
    exact (c8FourRecordData661_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData662).card = 2 ^ c8FourRecordData662.generators.length
    rw [(c8FourRecordData662_rank_card).2]
    exact (c8FourRecordData662_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData663).card = 2 ^ c8FourRecordData663.generators.length
    rw [(c8FourRecordData663_rank_card).2]
    exact (c8FourRecordData663_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData664).card = 2 ^ c8FourRecordData664.generators.length
    rw [(c8FourRecordData664_rank_card).2]
    exact (c8FourRecordData664_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData665).card = 2 ^ c8FourRecordData665.generators.length
    rw [(c8FourRecordData665_rank_card).2]
    exact (c8FourRecordData665_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData666).card = 2 ^ c8FourRecordData666.generators.length
    rw [(c8FourRecordData666_rank_card).2]
    exact (c8FourRecordData666_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData667).card = 2 ^ c8FourRecordData667.generators.length
    rw [(c8FourRecordData667_rank_card).2]
    exact (c8FourRecordData667_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData668).card = 2 ^ c8FourRecordData668.generators.length
    rw [(c8FourRecordData668_rank_card).2]
    exact (c8FourRecordData668_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData669).card = 2 ^ c8FourRecordData669.generators.length
    rw [(c8FourRecordData669_rank_card).2]
    exact (c8FourRecordData669_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData670).card = 2 ^ c8FourRecordData670.generators.length
    rw [(c8FourRecordData670_rank_card).2]
    exact (c8FourRecordData670_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData671).card = 2 ^ c8FourRecordData671.generators.length
    rw [(c8FourRecordData671_rank_card).2]
    exact (c8FourRecordData671_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData672).card = 2 ^ c8FourRecordData672.generators.length
    rw [(c8FourRecordData672_rank_card).2]
    exact (c8FourRecordData672_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData673).card = 2 ^ c8FourRecordData673.generators.length
    rw [(c8FourRecordData673_rank_card).2]
    exact (c8FourRecordData673_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData674).card = 2 ^ c8FourRecordData674.generators.length
    rw [(c8FourRecordData674_rank_card).2]
    exact (c8FourRecordData674_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData675).card = 2 ^ c8FourRecordData675.generators.length
    rw [(c8FourRecordData675_rank_card).2]
    exact (c8FourRecordData675_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData676).card = 2 ^ c8FourRecordData676.generators.length
    rw [(c8FourRecordData676_rank_card).2]
    exact (c8FourRecordData676_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData677).card = 2 ^ c8FourRecordData677.generators.length
    rw [(c8FourRecordData677_rank_card).2]
    exact (c8FourRecordData677_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData678).card = 2 ^ c8FourRecordData678.generators.length
    rw [(c8FourRecordData678_rank_card).2]
    exact (c8FourRecordData678_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData679).card = 2 ^ c8FourRecordData679.generators.length
    rw [(c8FourRecordData679_rank_card).2]
    exact (c8FourRecordData679_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData680).card = 2 ^ c8FourRecordData680.generators.length
    rw [(c8FourRecordData680_rank_card).2]
    exact (c8FourRecordData680_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData681).card = 2 ^ c8FourRecordData681.generators.length
    rw [(c8FourRecordData681_rank_card).2]
    exact (c8FourRecordData681_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData682).card = 2 ^ c8FourRecordData682.generators.length
    rw [(c8FourRecordData682_rank_card).2]
    exact (c8FourRecordData682_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData683).card = 2 ^ c8FourRecordData683.generators.length
    rw [(c8FourRecordData683_rank_card).2]
    exact (c8FourRecordData683_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData684).card = 2 ^ c8FourRecordData684.generators.length
    rw [(c8FourRecordData684_rank_card).2]
    exact (c8FourRecordData684_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData685).card = 2 ^ c8FourRecordData685.generators.length
    rw [(c8FourRecordData685_rank_card).2]
    exact (c8FourRecordData685_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData686).card = 2 ^ c8FourRecordData686.generators.length
    rw [(c8FourRecordData686_rank_card).2]
    exact (c8FourRecordData686_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData687).card = 2 ^ c8FourRecordData687.generators.length
    rw [(c8FourRecordData687_rank_card).2]
    exact (c8FourRecordData687_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData688).card = 2 ^ c8FourRecordData688.generators.length
    rw [(c8FourRecordData688_rank_card).2]
    exact (c8FourRecordData688_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData689).card = 2 ^ c8FourRecordData689.generators.length
    rw [(c8FourRecordData689_rank_card).2]
    exact (c8FourRecordData689_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData690).card = 2 ^ c8FourRecordData690.generators.length
    rw [(c8FourRecordData690_rank_card).2]
    exact (c8FourRecordData690_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData691).card = 2 ^ c8FourRecordData691.generators.length
    rw [(c8FourRecordData691_rank_card).2]
    exact (c8FourRecordData691_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData692).card = 2 ^ c8FourRecordData692.generators.length
    rw [(c8FourRecordData692_rank_card).2]
    exact (c8FourRecordData692_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData693).card = 2 ^ c8FourRecordData693.generators.length
    rw [(c8FourRecordData693_rank_card).2]
    exact (c8FourRecordData693_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData694).card = 2 ^ c8FourRecordData694.generators.length
    rw [(c8FourRecordData694_rank_card).2]
    exact (c8FourRecordData694_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData695).card = 2 ^ c8FourRecordData695.generators.length
    rw [(c8FourRecordData695_rank_card).2]
    exact (c8FourRecordData695_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData696).card = 2 ^ c8FourRecordData696.generators.length
    rw [(c8FourRecordData696_rank_card).2]
    exact (c8FourRecordData696_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData697).card = 2 ^ c8FourRecordData697.generators.length
    rw [(c8FourRecordData697_rank_card).2]
    exact (c8FourRecordData697_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData698).card = 2 ^ c8FourRecordData698.generators.length
    rw [(c8FourRecordData698_rank_card).2]
    exact (c8FourRecordData698_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData699).card = 2 ^ c8FourRecordData699.generators.length
    rw [(c8FourRecordData699_rank_card).2]
    exact (c8FourRecordData699_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData700).card = 2 ^ c8FourRecordData700.generators.length
    rw [(c8FourRecordData700_rank_card).2]
    exact (c8FourRecordData700_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData701).card = 2 ^ c8FourRecordData701.generators.length
    rw [(c8FourRecordData701_rank_card).2]
    exact (c8FourRecordData701_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData702).card = 2 ^ c8FourRecordData702.generators.length
    rw [(c8FourRecordData702_rank_card).2]
    exact (c8FourRecordData702_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData703).card = 2 ^ c8FourRecordData703.generators.length
    rw [(c8FourRecordData703_rank_card).2]
    exact (c8FourRecordData703_rank_card).1

end CFSG.LargeEvenClassification.Helpers
