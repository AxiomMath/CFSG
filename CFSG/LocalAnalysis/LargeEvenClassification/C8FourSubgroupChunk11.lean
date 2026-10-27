module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupValid11
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupKernel11
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRank11

public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk11_valid (j : Fin 64) :
    c8FourRecordValid (c8FourRecordChunk11[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData704_valid
  · exact c8FourRecordData705_valid
  · exact c8FourRecordData706_valid
  · exact c8FourRecordData707_valid
  · exact c8FourRecordData708_valid
  · exact c8FourRecordData709_valid
  · exact c8FourRecordData710_valid
  · exact c8FourRecordData711_valid
  · exact c8FourRecordData712_valid
  · exact c8FourRecordData713_valid
  · exact c8FourRecordData714_valid
  · exact c8FourRecordData715_valid
  · exact c8FourRecordData716_valid
  · exact c8FourRecordData717_valid
  · exact c8FourRecordData718_valid
  · exact c8FourRecordData719_valid
  · exact c8FourRecordData720_valid
  · exact c8FourRecordData721_valid
  · exact c8FourRecordData722_valid
  · exact c8FourRecordData723_valid
  · exact c8FourRecordData724_valid
  · exact c8FourRecordData725_valid
  · exact c8FourRecordData726_valid
  · exact c8FourRecordData727_valid
  · exact c8FourRecordData728_valid
  · exact c8FourRecordData729_valid
  · exact c8FourRecordData730_valid
  · exact c8FourRecordData731_valid
  · exact c8FourRecordData732_valid
  · exact c8FourRecordData733_valid
  · exact c8FourRecordData734_valid
  · exact c8FourRecordData735_valid
  · exact c8FourRecordData736_valid
  · exact c8FourRecordData737_valid
  · exact c8FourRecordData738_valid
  · exact c8FourRecordData739_valid
  · exact c8FourRecordData740_valid
  · exact c8FourRecordData741_valid
  · exact c8FourRecordData742_valid
  · exact c8FourRecordData743_valid
  · exact c8FourRecordData744_valid
  · exact c8FourRecordData745_valid
  · exact c8FourRecordData746_valid
  · exact c8FourRecordData747_valid
  · exact c8FourRecordData748_valid
  · exact c8FourRecordData749_valid
  · exact c8FourRecordData750_valid
  · exact c8FourRecordData751_valid
  · exact c8FourRecordData752_valid
  · exact c8FourRecordData753_valid
  · exact c8FourRecordData754_valid
  · exact c8FourRecordData755_valid
  · exact c8FourRecordData756_valid
  · exact c8FourRecordData757_valid
  · exact c8FourRecordData758_valid
  · exact c8FourRecordData759_valid
  · exact c8FourRecordData760_valid
  · exact c8FourRecordData761_valid
  · exact c8FourRecordData762_valid
  · exact c8FourRecordData763_valid
  · exact c8FourRecordData764_valid
  · exact c8FourRecordData765_valid
  · exact c8FourRecordData766_valid
  · exact c8FourRecordData767_valid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk11_kernels (j : Fin 64) :
    c8FourKernelListsValid (c8FourRecordChunk11[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData704_kernels
  · exact c8FourRecordData705_kernels
  · exact c8FourRecordData706_kernels
  · exact c8FourRecordData707_kernels
  · exact c8FourRecordData708_kernels
  · exact c8FourRecordData709_kernels
  · exact c8FourRecordData710_kernels
  · exact c8FourRecordData711_kernels
  · exact c8FourRecordData712_kernels
  · exact c8FourRecordData713_kernels
  · exact c8FourRecordData714_kernels
  · exact c8FourRecordData715_kernels
  · exact c8FourRecordData716_kernels
  · exact c8FourRecordData717_kernels
  · exact c8FourRecordData718_kernels
  · exact c8FourRecordData719_kernels
  · exact c8FourRecordData720_kernels
  · exact c8FourRecordData721_kernels
  · exact c8FourRecordData722_kernels
  · exact c8FourRecordData723_kernels
  · exact c8FourRecordData724_kernels
  · exact c8FourRecordData725_kernels
  · exact c8FourRecordData726_kernels
  · exact c8FourRecordData727_kernels
  · exact c8FourRecordData728_kernels
  · exact c8FourRecordData729_kernels
  · exact c8FourRecordData730_kernels
  · exact c8FourRecordData731_kernels
  · exact c8FourRecordData732_kernels
  · exact c8FourRecordData733_kernels
  · exact c8FourRecordData734_kernels
  · exact c8FourRecordData735_kernels
  · exact c8FourRecordData736_kernels
  · exact c8FourRecordData737_kernels
  · exact c8FourRecordData738_kernels
  · exact c8FourRecordData739_kernels
  · exact c8FourRecordData740_kernels
  · exact c8FourRecordData741_kernels
  · exact c8FourRecordData742_kernels
  · exact c8FourRecordData743_kernels
  · exact c8FourRecordData744_kernels
  · exact c8FourRecordData745_kernels
  · exact c8FourRecordData746_kernels
  · exact c8FourRecordData747_kernels
  · exact c8FourRecordData748_kernels
  · exact c8FourRecordData749_kernels
  · exact c8FourRecordData750_kernels
  · exact c8FourRecordData751_kernels
  · exact c8FourRecordData752_kernels
  · exact c8FourRecordData753_kernels
  · exact c8FourRecordData754_kernels
  · exact c8FourRecordData755_kernels
  · exact c8FourRecordData756_kernels
  · exact c8FourRecordData757_kernels
  · exact c8FourRecordData758_kernels
  · exact c8FourRecordData759_kernels
  · exact c8FourRecordData760_kernels
  · exact c8FourRecordData761_kernels
  · exact c8FourRecordData762_kernels
  · exact c8FourRecordData763_kernels
  · exact c8FourRecordData764_kernels
  · exact c8FourRecordData765_kernels
  · exact c8FourRecordData766_kernels
  · exact c8FourRecordData767_kernels

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk11_vectors (j : Fin 64) :
    c8FourGeneratorVectorsValid (c8FourRecordChunk11[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData704_vectors
  · exact c8FourRecordData705_vectors
  · exact c8FourRecordData706_vectors
  · exact c8FourRecordData707_vectors
  · exact c8FourRecordData708_vectors
  · exact c8FourRecordData709_vectors
  · exact c8FourRecordData710_vectors
  · exact c8FourRecordData711_vectors
  · exact c8FourRecordData712_vectors
  · exact c8FourRecordData713_vectors
  · exact c8FourRecordData714_vectors
  · exact c8FourRecordData715_vectors
  · exact c8FourRecordData716_vectors
  · exact c8FourRecordData717_vectors
  · exact c8FourRecordData718_vectors
  · exact c8FourRecordData719_vectors
  · exact c8FourRecordData720_vectors
  · exact c8FourRecordData721_vectors
  · exact c8FourRecordData722_vectors
  · exact c8FourRecordData723_vectors
  · exact c8FourRecordData724_vectors
  · exact c8FourRecordData725_vectors
  · exact c8FourRecordData726_vectors
  · exact c8FourRecordData727_vectors
  · exact c8FourRecordData728_vectors
  · exact c8FourRecordData729_vectors
  · exact c8FourRecordData730_vectors
  · exact c8FourRecordData731_vectors
  · exact c8FourRecordData732_vectors
  · exact c8FourRecordData733_vectors
  · exact c8FourRecordData734_vectors
  · exact c8FourRecordData735_vectors
  · exact c8FourRecordData736_vectors
  · exact c8FourRecordData737_vectors
  · exact c8FourRecordData738_vectors
  · exact c8FourRecordData739_vectors
  · exact c8FourRecordData740_vectors
  · exact c8FourRecordData741_vectors
  · exact c8FourRecordData742_vectors
  · exact c8FourRecordData743_vectors
  · exact c8FourRecordData744_vectors
  · exact c8FourRecordData745_vectors
  · exact c8FourRecordData746_vectors
  · exact c8FourRecordData747_vectors
  · exact c8FourRecordData748_vectors
  · exact c8FourRecordData749_vectors
  · exact c8FourRecordData750_vectors
  · exact c8FourRecordData751_vectors
  · exact c8FourRecordData752_vectors
  · exact c8FourRecordData753_vectors
  · exact c8FourRecordData754_vectors
  · exact c8FourRecordData755_vectors
  · exact c8FourRecordData756_vectors
  · exact c8FourRecordData757_vectors
  · exact c8FourRecordData758_vectors
  · exact c8FourRecordData759_vectors
  · exact c8FourRecordData760_vectors
  · exact c8FourRecordData761_vectors
  · exact c8FourRecordData762_vectors
  · exact c8FourRecordData763_vectors
  · exact c8FourRecordData764_vectors
  · exact c8FourRecordData765_vectors
  · exact c8FourRecordData766_vectors
  · exact c8FourRecordData767_vectors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk11_rank_cards (j : Fin 64) :
    (c8FourRecordBinaryImages (c8FourRecordChunk11[j.val]!)).card = 2 ^ (c8FourRecordChunk11[j.val]!).generators.length := by
  fin_cases j
  · change (c8FourRecordBinaryImages c8FourRecordData704).card = 2 ^ c8FourRecordData704.generators.length
    rw [(c8FourRecordData704_rank_card).2]
    exact (c8FourRecordData704_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData705).card = 2 ^ c8FourRecordData705.generators.length
    rw [(c8FourRecordData705_rank_card).2]
    exact (c8FourRecordData705_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData706).card = 2 ^ c8FourRecordData706.generators.length
    rw [(c8FourRecordData706_rank_card).2]
    exact (c8FourRecordData706_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData707).card = 2 ^ c8FourRecordData707.generators.length
    rw [(c8FourRecordData707_rank_card).2]
    exact (c8FourRecordData707_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData708).card = 2 ^ c8FourRecordData708.generators.length
    rw [(c8FourRecordData708_rank_card).2]
    exact (c8FourRecordData708_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData709).card = 2 ^ c8FourRecordData709.generators.length
    rw [(c8FourRecordData709_rank_card).2]
    exact (c8FourRecordData709_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData710).card = 2 ^ c8FourRecordData710.generators.length
    rw [(c8FourRecordData710_rank_card).2]
    exact (c8FourRecordData710_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData711).card = 2 ^ c8FourRecordData711.generators.length
    rw [(c8FourRecordData711_rank_card).2]
    exact (c8FourRecordData711_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData712).card = 2 ^ c8FourRecordData712.generators.length
    rw [(c8FourRecordData712_rank_card).2]
    exact (c8FourRecordData712_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData713).card = 2 ^ c8FourRecordData713.generators.length
    rw [(c8FourRecordData713_rank_card).2]
    exact (c8FourRecordData713_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData714).card = 2 ^ c8FourRecordData714.generators.length
    rw [(c8FourRecordData714_rank_card).2]
    exact (c8FourRecordData714_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData715).card = 2 ^ c8FourRecordData715.generators.length
    rw [(c8FourRecordData715_rank_card).2]
    exact (c8FourRecordData715_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData716).card = 2 ^ c8FourRecordData716.generators.length
    rw [(c8FourRecordData716_rank_card).2]
    exact (c8FourRecordData716_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData717).card = 2 ^ c8FourRecordData717.generators.length
    rw [(c8FourRecordData717_rank_card).2]
    exact (c8FourRecordData717_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData718).card = 2 ^ c8FourRecordData718.generators.length
    rw [(c8FourRecordData718_rank_card).2]
    exact (c8FourRecordData718_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData719).card = 2 ^ c8FourRecordData719.generators.length
    rw [(c8FourRecordData719_rank_card).2]
    exact (c8FourRecordData719_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData720).card = 2 ^ c8FourRecordData720.generators.length
    rw [(c8FourRecordData720_rank_card).2]
    exact (c8FourRecordData720_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData721).card = 2 ^ c8FourRecordData721.generators.length
    rw [(c8FourRecordData721_rank_card).2]
    exact (c8FourRecordData721_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData722).card = 2 ^ c8FourRecordData722.generators.length
    rw [(c8FourRecordData722_rank_card).2]
    exact (c8FourRecordData722_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData723).card = 2 ^ c8FourRecordData723.generators.length
    rw [(c8FourRecordData723_rank_card).2]
    exact (c8FourRecordData723_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData724).card = 2 ^ c8FourRecordData724.generators.length
    rw [(c8FourRecordData724_rank_card).2]
    exact (c8FourRecordData724_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData725).card = 2 ^ c8FourRecordData725.generators.length
    rw [(c8FourRecordData725_rank_card).2]
    exact (c8FourRecordData725_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData726).card = 2 ^ c8FourRecordData726.generators.length
    rw [(c8FourRecordData726_rank_card).2]
    exact (c8FourRecordData726_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData727).card = 2 ^ c8FourRecordData727.generators.length
    rw [(c8FourRecordData727_rank_card).2]
    exact (c8FourRecordData727_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData728).card = 2 ^ c8FourRecordData728.generators.length
    rw [(c8FourRecordData728_rank_card).2]
    exact (c8FourRecordData728_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData729).card = 2 ^ c8FourRecordData729.generators.length
    rw [(c8FourRecordData729_rank_card).2]
    exact (c8FourRecordData729_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData730).card = 2 ^ c8FourRecordData730.generators.length
    rw [(c8FourRecordData730_rank_card).2]
    exact (c8FourRecordData730_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData731).card = 2 ^ c8FourRecordData731.generators.length
    rw [(c8FourRecordData731_rank_card).2]
    exact (c8FourRecordData731_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData732).card = 2 ^ c8FourRecordData732.generators.length
    rw [(c8FourRecordData732_rank_card).2]
    exact (c8FourRecordData732_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData733).card = 2 ^ c8FourRecordData733.generators.length
    rw [(c8FourRecordData733_rank_card).2]
    exact (c8FourRecordData733_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData734).card = 2 ^ c8FourRecordData734.generators.length
    rw [(c8FourRecordData734_rank_card).2]
    exact (c8FourRecordData734_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData735).card = 2 ^ c8FourRecordData735.generators.length
    rw [(c8FourRecordData735_rank_card).2]
    exact (c8FourRecordData735_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData736).card = 2 ^ c8FourRecordData736.generators.length
    rw [(c8FourRecordData736_rank_card).2]
    exact (c8FourRecordData736_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData737).card = 2 ^ c8FourRecordData737.generators.length
    rw [(c8FourRecordData737_rank_card).2]
    exact (c8FourRecordData737_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData738).card = 2 ^ c8FourRecordData738.generators.length
    rw [(c8FourRecordData738_rank_card).2]
    exact (c8FourRecordData738_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData739).card = 2 ^ c8FourRecordData739.generators.length
    rw [(c8FourRecordData739_rank_card).2]
    exact (c8FourRecordData739_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData740).card = 2 ^ c8FourRecordData740.generators.length
    rw [(c8FourRecordData740_rank_card).2]
    exact (c8FourRecordData740_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData741).card = 2 ^ c8FourRecordData741.generators.length
    rw [(c8FourRecordData741_rank_card).2]
    exact (c8FourRecordData741_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData742).card = 2 ^ c8FourRecordData742.generators.length
    rw [(c8FourRecordData742_rank_card).2]
    exact (c8FourRecordData742_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData743).card = 2 ^ c8FourRecordData743.generators.length
    rw [(c8FourRecordData743_rank_card).2]
    exact (c8FourRecordData743_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData744).card = 2 ^ c8FourRecordData744.generators.length
    rw [(c8FourRecordData744_rank_card).2]
    exact (c8FourRecordData744_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData745).card = 2 ^ c8FourRecordData745.generators.length
    rw [(c8FourRecordData745_rank_card).2]
    exact (c8FourRecordData745_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData746).card = 2 ^ c8FourRecordData746.generators.length
    rw [(c8FourRecordData746_rank_card).2]
    exact (c8FourRecordData746_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData747).card = 2 ^ c8FourRecordData747.generators.length
    rw [(c8FourRecordData747_rank_card).2]
    exact (c8FourRecordData747_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData748).card = 2 ^ c8FourRecordData748.generators.length
    rw [(c8FourRecordData748_rank_card).2]
    exact (c8FourRecordData748_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData749).card = 2 ^ c8FourRecordData749.generators.length
    rw [(c8FourRecordData749_rank_card).2]
    exact (c8FourRecordData749_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData750).card = 2 ^ c8FourRecordData750.generators.length
    rw [(c8FourRecordData750_rank_card).2]
    exact (c8FourRecordData750_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData751).card = 2 ^ c8FourRecordData751.generators.length
    rw [(c8FourRecordData751_rank_card).2]
    exact (c8FourRecordData751_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData752).card = 2 ^ c8FourRecordData752.generators.length
    rw [(c8FourRecordData752_rank_card).2]
    exact (c8FourRecordData752_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData753).card = 2 ^ c8FourRecordData753.generators.length
    rw [(c8FourRecordData753_rank_card).2]
    exact (c8FourRecordData753_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData754).card = 2 ^ c8FourRecordData754.generators.length
    rw [(c8FourRecordData754_rank_card).2]
    exact (c8FourRecordData754_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData755).card = 2 ^ c8FourRecordData755.generators.length
    rw [(c8FourRecordData755_rank_card).2]
    exact (c8FourRecordData755_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData756).card = 2 ^ c8FourRecordData756.generators.length
    rw [(c8FourRecordData756_rank_card).2]
    exact (c8FourRecordData756_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData757).card = 2 ^ c8FourRecordData757.generators.length
    rw [(c8FourRecordData757_rank_card).2]
    exact (c8FourRecordData757_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData758).card = 2 ^ c8FourRecordData758.generators.length
    rw [(c8FourRecordData758_rank_card).2]
    exact (c8FourRecordData758_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData759).card = 2 ^ c8FourRecordData759.generators.length
    rw [(c8FourRecordData759_rank_card).2]
    exact (c8FourRecordData759_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData760).card = 2 ^ c8FourRecordData760.generators.length
    rw [(c8FourRecordData760_rank_card).2]
    exact (c8FourRecordData760_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData761).card = 2 ^ c8FourRecordData761.generators.length
    rw [(c8FourRecordData761_rank_card).2]
    exact (c8FourRecordData761_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData762).card = 2 ^ c8FourRecordData762.generators.length
    rw [(c8FourRecordData762_rank_card).2]
    exact (c8FourRecordData762_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData763).card = 2 ^ c8FourRecordData763.generators.length
    rw [(c8FourRecordData763_rank_card).2]
    exact (c8FourRecordData763_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData764).card = 2 ^ c8FourRecordData764.generators.length
    rw [(c8FourRecordData764_rank_card).2]
    exact (c8FourRecordData764_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData765).card = 2 ^ c8FourRecordData765.generators.length
    rw [(c8FourRecordData765_rank_card).2]
    exact (c8FourRecordData765_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData766).card = 2 ^ c8FourRecordData766.generators.length
    rw [(c8FourRecordData766_rank_card).2]
    exact (c8FourRecordData766_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData767).card = 2 ^ c8FourRecordData767.generators.length
    rw [(c8FourRecordData767_rank_card).2]
    exact (c8FourRecordData767_rank_card).1

end CFSG.LargeEvenClassification.Helpers
