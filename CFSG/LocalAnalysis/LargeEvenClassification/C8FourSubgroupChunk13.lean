module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupValid13
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupKernel13
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRank13

public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk13_valid (j : Fin 64) :
    c8FourRecordValid (c8FourRecordChunk13[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData832_valid
  · exact c8FourRecordData833_valid
  · exact c8FourRecordData834_valid
  · exact c8FourRecordData835_valid
  · exact c8FourRecordData836_valid
  · exact c8FourRecordData837_valid
  · exact c8FourRecordData838_valid
  · exact c8FourRecordData839_valid
  · exact c8FourRecordData840_valid
  · exact c8FourRecordData841_valid
  · exact c8FourRecordData842_valid
  · exact c8FourRecordData843_valid
  · exact c8FourRecordData844_valid
  · exact c8FourRecordData845_valid
  · exact c8FourRecordData846_valid
  · exact c8FourRecordData847_valid
  · exact c8FourRecordData848_valid
  · exact c8FourRecordData849_valid
  · exact c8FourRecordData850_valid
  · exact c8FourRecordData851_valid
  · exact c8FourRecordData852_valid
  · exact c8FourRecordData853_valid
  · exact c8FourRecordData854_valid
  · exact c8FourRecordData855_valid
  · exact c8FourRecordData856_valid
  · exact c8FourRecordData857_valid
  · exact c8FourRecordData858_valid
  · exact c8FourRecordData859_valid
  · exact c8FourRecordData860_valid
  · exact c8FourRecordData861_valid
  · exact c8FourRecordData862_valid
  · exact c8FourRecordData863_valid
  · exact c8FourRecordData864_valid
  · exact c8FourRecordData865_valid
  · exact c8FourRecordData866_valid
  · exact c8FourRecordData867_valid
  · exact c8FourRecordData868_valid
  · exact c8FourRecordData869_valid
  · exact c8FourRecordData870_valid
  · exact c8FourRecordData871_valid
  · exact c8FourRecordData872_valid
  · exact c8FourRecordData873_valid
  · exact c8FourRecordData874_valid
  · exact c8FourRecordData875_valid
  · exact c8FourRecordData876_valid
  · exact c8FourRecordData877_valid
  · exact c8FourRecordData878_valid
  · exact c8FourRecordData879_valid
  · exact c8FourRecordData880_valid
  · exact c8FourRecordData881_valid
  · exact c8FourRecordData882_valid
  · exact c8FourRecordData883_valid
  · exact c8FourRecordData884_valid
  · exact c8FourRecordData885_valid
  · exact c8FourRecordData886_valid
  · exact c8FourRecordData887_valid
  · exact c8FourRecordData888_valid
  · exact c8FourRecordData889_valid
  · exact c8FourRecordData890_valid
  · exact c8FourRecordData891_valid
  · exact c8FourRecordData892_valid
  · exact c8FourRecordData893_valid
  · exact c8FourRecordData894_valid
  · exact c8FourRecordData895_valid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk13_kernels (j : Fin 64) :
    c8FourKernelListsValid (c8FourRecordChunk13[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData832_kernels
  · exact c8FourRecordData833_kernels
  · exact c8FourRecordData834_kernels
  · exact c8FourRecordData835_kernels
  · exact c8FourRecordData836_kernels
  · exact c8FourRecordData837_kernels
  · exact c8FourRecordData838_kernels
  · exact c8FourRecordData839_kernels
  · exact c8FourRecordData840_kernels
  · exact c8FourRecordData841_kernels
  · exact c8FourRecordData842_kernels
  · exact c8FourRecordData843_kernels
  · exact c8FourRecordData844_kernels
  · exact c8FourRecordData845_kernels
  · exact c8FourRecordData846_kernels
  · exact c8FourRecordData847_kernels
  · exact c8FourRecordData848_kernels
  · exact c8FourRecordData849_kernels
  · exact c8FourRecordData850_kernels
  · exact c8FourRecordData851_kernels
  · exact c8FourRecordData852_kernels
  · exact c8FourRecordData853_kernels
  · exact c8FourRecordData854_kernels
  · exact c8FourRecordData855_kernels
  · exact c8FourRecordData856_kernels
  · exact c8FourRecordData857_kernels
  · exact c8FourRecordData858_kernels
  · exact c8FourRecordData859_kernels
  · exact c8FourRecordData860_kernels
  · exact c8FourRecordData861_kernels
  · exact c8FourRecordData862_kernels
  · exact c8FourRecordData863_kernels
  · exact c8FourRecordData864_kernels
  · exact c8FourRecordData865_kernels
  · exact c8FourRecordData866_kernels
  · exact c8FourRecordData867_kernels
  · exact c8FourRecordData868_kernels
  · exact c8FourRecordData869_kernels
  · exact c8FourRecordData870_kernels
  · exact c8FourRecordData871_kernels
  · exact c8FourRecordData872_kernels
  · exact c8FourRecordData873_kernels
  · exact c8FourRecordData874_kernels
  · exact c8FourRecordData875_kernels
  · exact c8FourRecordData876_kernels
  · exact c8FourRecordData877_kernels
  · exact c8FourRecordData878_kernels
  · exact c8FourRecordData879_kernels
  · exact c8FourRecordData880_kernels
  · exact c8FourRecordData881_kernels
  · exact c8FourRecordData882_kernels
  · exact c8FourRecordData883_kernels
  · exact c8FourRecordData884_kernels
  · exact c8FourRecordData885_kernels
  · exact c8FourRecordData886_kernels
  · exact c8FourRecordData887_kernels
  · exact c8FourRecordData888_kernels
  · exact c8FourRecordData889_kernels
  · exact c8FourRecordData890_kernels
  · exact c8FourRecordData891_kernels
  · exact c8FourRecordData892_kernels
  · exact c8FourRecordData893_kernels
  · exact c8FourRecordData894_kernels
  · exact c8FourRecordData895_kernels

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk13_vectors (j : Fin 64) :
    c8FourGeneratorVectorsValid (c8FourRecordChunk13[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData832_vectors
  · exact c8FourRecordData833_vectors
  · exact c8FourRecordData834_vectors
  · exact c8FourRecordData835_vectors
  · exact c8FourRecordData836_vectors
  · exact c8FourRecordData837_vectors
  · exact c8FourRecordData838_vectors
  · exact c8FourRecordData839_vectors
  · exact c8FourRecordData840_vectors
  · exact c8FourRecordData841_vectors
  · exact c8FourRecordData842_vectors
  · exact c8FourRecordData843_vectors
  · exact c8FourRecordData844_vectors
  · exact c8FourRecordData845_vectors
  · exact c8FourRecordData846_vectors
  · exact c8FourRecordData847_vectors
  · exact c8FourRecordData848_vectors
  · exact c8FourRecordData849_vectors
  · exact c8FourRecordData850_vectors
  · exact c8FourRecordData851_vectors
  · exact c8FourRecordData852_vectors
  · exact c8FourRecordData853_vectors
  · exact c8FourRecordData854_vectors
  · exact c8FourRecordData855_vectors
  · exact c8FourRecordData856_vectors
  · exact c8FourRecordData857_vectors
  · exact c8FourRecordData858_vectors
  · exact c8FourRecordData859_vectors
  · exact c8FourRecordData860_vectors
  · exact c8FourRecordData861_vectors
  · exact c8FourRecordData862_vectors
  · exact c8FourRecordData863_vectors
  · exact c8FourRecordData864_vectors
  · exact c8FourRecordData865_vectors
  · exact c8FourRecordData866_vectors
  · exact c8FourRecordData867_vectors
  · exact c8FourRecordData868_vectors
  · exact c8FourRecordData869_vectors
  · exact c8FourRecordData870_vectors
  · exact c8FourRecordData871_vectors
  · exact c8FourRecordData872_vectors
  · exact c8FourRecordData873_vectors
  · exact c8FourRecordData874_vectors
  · exact c8FourRecordData875_vectors
  · exact c8FourRecordData876_vectors
  · exact c8FourRecordData877_vectors
  · exact c8FourRecordData878_vectors
  · exact c8FourRecordData879_vectors
  · exact c8FourRecordData880_vectors
  · exact c8FourRecordData881_vectors
  · exact c8FourRecordData882_vectors
  · exact c8FourRecordData883_vectors
  · exact c8FourRecordData884_vectors
  · exact c8FourRecordData885_vectors
  · exact c8FourRecordData886_vectors
  · exact c8FourRecordData887_vectors
  · exact c8FourRecordData888_vectors
  · exact c8FourRecordData889_vectors
  · exact c8FourRecordData890_vectors
  · exact c8FourRecordData891_vectors
  · exact c8FourRecordData892_vectors
  · exact c8FourRecordData893_vectors
  · exact c8FourRecordData894_vectors
  · exact c8FourRecordData895_vectors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk13_rank_cards (j : Fin 64) :
    (c8FourRecordBinaryImages (c8FourRecordChunk13[j.val]!)).card = 2 ^ (c8FourRecordChunk13[j.val]!).generators.length := by
  fin_cases j
  · change (c8FourRecordBinaryImages c8FourRecordData832).card = 2 ^ c8FourRecordData832.generators.length
    rw [(c8FourRecordData832_rank_card).2]
    exact (c8FourRecordData832_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData833).card = 2 ^ c8FourRecordData833.generators.length
    rw [(c8FourRecordData833_rank_card).2]
    exact (c8FourRecordData833_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData834).card = 2 ^ c8FourRecordData834.generators.length
    rw [(c8FourRecordData834_rank_card).2]
    exact (c8FourRecordData834_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData835).card = 2 ^ c8FourRecordData835.generators.length
    rw [(c8FourRecordData835_rank_card).2]
    exact (c8FourRecordData835_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData836).card = 2 ^ c8FourRecordData836.generators.length
    rw [(c8FourRecordData836_rank_card).2]
    exact (c8FourRecordData836_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData837).card = 2 ^ c8FourRecordData837.generators.length
    rw [(c8FourRecordData837_rank_card).2]
    exact (c8FourRecordData837_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData838).card = 2 ^ c8FourRecordData838.generators.length
    rw [(c8FourRecordData838_rank_card).2]
    exact (c8FourRecordData838_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData839).card = 2 ^ c8FourRecordData839.generators.length
    rw [(c8FourRecordData839_rank_card).2]
    exact (c8FourRecordData839_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData840).card = 2 ^ c8FourRecordData840.generators.length
    rw [(c8FourRecordData840_rank_card).2]
    exact (c8FourRecordData840_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData841).card = 2 ^ c8FourRecordData841.generators.length
    rw [(c8FourRecordData841_rank_card).2]
    exact (c8FourRecordData841_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData842).card = 2 ^ c8FourRecordData842.generators.length
    rw [(c8FourRecordData842_rank_card).2]
    exact (c8FourRecordData842_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData843).card = 2 ^ c8FourRecordData843.generators.length
    rw [(c8FourRecordData843_rank_card).2]
    exact (c8FourRecordData843_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData844).card = 2 ^ c8FourRecordData844.generators.length
    rw [(c8FourRecordData844_rank_card).2]
    exact (c8FourRecordData844_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData845).card = 2 ^ c8FourRecordData845.generators.length
    rw [(c8FourRecordData845_rank_card).2]
    exact (c8FourRecordData845_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData846).card = 2 ^ c8FourRecordData846.generators.length
    rw [(c8FourRecordData846_rank_card).2]
    exact (c8FourRecordData846_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData847).card = 2 ^ c8FourRecordData847.generators.length
    rw [(c8FourRecordData847_rank_card).2]
    exact (c8FourRecordData847_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData848).card = 2 ^ c8FourRecordData848.generators.length
    rw [(c8FourRecordData848_rank_card).2]
    exact (c8FourRecordData848_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData849).card = 2 ^ c8FourRecordData849.generators.length
    rw [(c8FourRecordData849_rank_card).2]
    exact (c8FourRecordData849_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData850).card = 2 ^ c8FourRecordData850.generators.length
    rw [(c8FourRecordData850_rank_card).2]
    exact (c8FourRecordData850_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData851).card = 2 ^ c8FourRecordData851.generators.length
    rw [(c8FourRecordData851_rank_card).2]
    exact (c8FourRecordData851_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData852).card = 2 ^ c8FourRecordData852.generators.length
    rw [(c8FourRecordData852_rank_card).2]
    exact (c8FourRecordData852_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData853).card = 2 ^ c8FourRecordData853.generators.length
    rw [(c8FourRecordData853_rank_card).2]
    exact (c8FourRecordData853_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData854).card = 2 ^ c8FourRecordData854.generators.length
    rw [(c8FourRecordData854_rank_card).2]
    exact (c8FourRecordData854_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData855).card = 2 ^ c8FourRecordData855.generators.length
    rw [(c8FourRecordData855_rank_card).2]
    exact (c8FourRecordData855_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData856).card = 2 ^ c8FourRecordData856.generators.length
    rw [(c8FourRecordData856_rank_card).2]
    exact (c8FourRecordData856_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData857).card = 2 ^ c8FourRecordData857.generators.length
    rw [(c8FourRecordData857_rank_card).2]
    exact (c8FourRecordData857_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData858).card = 2 ^ c8FourRecordData858.generators.length
    rw [(c8FourRecordData858_rank_card).2]
    exact (c8FourRecordData858_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData859).card = 2 ^ c8FourRecordData859.generators.length
    rw [(c8FourRecordData859_rank_card).2]
    exact (c8FourRecordData859_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData860).card = 2 ^ c8FourRecordData860.generators.length
    rw [(c8FourRecordData860_rank_card).2]
    exact (c8FourRecordData860_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData861).card = 2 ^ c8FourRecordData861.generators.length
    rw [(c8FourRecordData861_rank_card).2]
    exact (c8FourRecordData861_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData862).card = 2 ^ c8FourRecordData862.generators.length
    rw [(c8FourRecordData862_rank_card).2]
    exact (c8FourRecordData862_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData863).card = 2 ^ c8FourRecordData863.generators.length
    rw [(c8FourRecordData863_rank_card).2]
    exact (c8FourRecordData863_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData864).card = 2 ^ c8FourRecordData864.generators.length
    rw [(c8FourRecordData864_rank_card).2]
    exact (c8FourRecordData864_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData865).card = 2 ^ c8FourRecordData865.generators.length
    rw [(c8FourRecordData865_rank_card).2]
    exact (c8FourRecordData865_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData866).card = 2 ^ c8FourRecordData866.generators.length
    rw [(c8FourRecordData866_rank_card).2]
    exact (c8FourRecordData866_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData867).card = 2 ^ c8FourRecordData867.generators.length
    rw [(c8FourRecordData867_rank_card).2]
    exact (c8FourRecordData867_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData868).card = 2 ^ c8FourRecordData868.generators.length
    rw [(c8FourRecordData868_rank_card).2]
    exact (c8FourRecordData868_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData869).card = 2 ^ c8FourRecordData869.generators.length
    rw [(c8FourRecordData869_rank_card).2]
    exact (c8FourRecordData869_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData870).card = 2 ^ c8FourRecordData870.generators.length
    rw [(c8FourRecordData870_rank_card).2]
    exact (c8FourRecordData870_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData871).card = 2 ^ c8FourRecordData871.generators.length
    rw [(c8FourRecordData871_rank_card).2]
    exact (c8FourRecordData871_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData872).card = 2 ^ c8FourRecordData872.generators.length
    rw [(c8FourRecordData872_rank_card).2]
    exact (c8FourRecordData872_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData873).card = 2 ^ c8FourRecordData873.generators.length
    rw [(c8FourRecordData873_rank_card).2]
    exact (c8FourRecordData873_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData874).card = 2 ^ c8FourRecordData874.generators.length
    rw [(c8FourRecordData874_rank_card).2]
    exact (c8FourRecordData874_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData875).card = 2 ^ c8FourRecordData875.generators.length
    rw [(c8FourRecordData875_rank_card).2]
    exact (c8FourRecordData875_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData876).card = 2 ^ c8FourRecordData876.generators.length
    rw [(c8FourRecordData876_rank_card).2]
    exact (c8FourRecordData876_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData877).card = 2 ^ c8FourRecordData877.generators.length
    rw [(c8FourRecordData877_rank_card).2]
    exact (c8FourRecordData877_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData878).card = 2 ^ c8FourRecordData878.generators.length
    rw [(c8FourRecordData878_rank_card).2]
    exact (c8FourRecordData878_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData879).card = 2 ^ c8FourRecordData879.generators.length
    rw [(c8FourRecordData879_rank_card).2]
    exact (c8FourRecordData879_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData880).card = 2 ^ c8FourRecordData880.generators.length
    rw [(c8FourRecordData880_rank_card).2]
    exact (c8FourRecordData880_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData881).card = 2 ^ c8FourRecordData881.generators.length
    rw [(c8FourRecordData881_rank_card).2]
    exact (c8FourRecordData881_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData882).card = 2 ^ c8FourRecordData882.generators.length
    rw [(c8FourRecordData882_rank_card).2]
    exact (c8FourRecordData882_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData883).card = 2 ^ c8FourRecordData883.generators.length
    rw [(c8FourRecordData883_rank_card).2]
    exact (c8FourRecordData883_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData884).card = 2 ^ c8FourRecordData884.generators.length
    rw [(c8FourRecordData884_rank_card).2]
    exact (c8FourRecordData884_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData885).card = 2 ^ c8FourRecordData885.generators.length
    rw [(c8FourRecordData885_rank_card).2]
    exact (c8FourRecordData885_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData886).card = 2 ^ c8FourRecordData886.generators.length
    rw [(c8FourRecordData886_rank_card).2]
    exact (c8FourRecordData886_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData887).card = 2 ^ c8FourRecordData887.generators.length
    rw [(c8FourRecordData887_rank_card).2]
    exact (c8FourRecordData887_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData888).card = 2 ^ c8FourRecordData888.generators.length
    rw [(c8FourRecordData888_rank_card).2]
    exact (c8FourRecordData888_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData889).card = 2 ^ c8FourRecordData889.generators.length
    rw [(c8FourRecordData889_rank_card).2]
    exact (c8FourRecordData889_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData890).card = 2 ^ c8FourRecordData890.generators.length
    rw [(c8FourRecordData890_rank_card).2]
    exact (c8FourRecordData890_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData891).card = 2 ^ c8FourRecordData891.generators.length
    rw [(c8FourRecordData891_rank_card).2]
    exact (c8FourRecordData891_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData892).card = 2 ^ c8FourRecordData892.generators.length
    rw [(c8FourRecordData892_rank_card).2]
    exact (c8FourRecordData892_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData893).card = 2 ^ c8FourRecordData893.generators.length
    rw [(c8FourRecordData893_rank_card).2]
    exact (c8FourRecordData893_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData894).card = 2 ^ c8FourRecordData894.generators.length
    rw [(c8FourRecordData894_rank_card).2]
    exact (c8FourRecordData894_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData895).card = 2 ^ c8FourRecordData895.generators.length
    rw [(c8FourRecordData895_rank_card).2]
    exact (c8FourRecordData895_rank_card).1

end CFSG.LargeEvenClassification.Helpers
