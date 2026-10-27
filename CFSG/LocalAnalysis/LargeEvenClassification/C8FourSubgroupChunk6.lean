module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupValid6
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupKernel6
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRank6

public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk6_valid (j : Fin 64) :
    c8FourRecordValid (c8FourRecordChunk6[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData384_valid
  · exact c8FourRecordData385_valid
  · exact c8FourRecordData386_valid
  · exact c8FourRecordData387_valid
  · exact c8FourRecordData388_valid
  · exact c8FourRecordData389_valid
  · exact c8FourRecordData390_valid
  · exact c8FourRecordData391_valid
  · exact c8FourRecordData392_valid
  · exact c8FourRecordData393_valid
  · exact c8FourRecordData394_valid
  · exact c8FourRecordData395_valid
  · exact c8FourRecordData396_valid
  · exact c8FourRecordData397_valid
  · exact c8FourRecordData398_valid
  · exact c8FourRecordData399_valid
  · exact c8FourRecordData400_valid
  · exact c8FourRecordData401_valid
  · exact c8FourRecordData402_valid
  · exact c8FourRecordData403_valid
  · exact c8FourRecordData404_valid
  · exact c8FourRecordData405_valid
  · exact c8FourRecordData406_valid
  · exact c8FourRecordData407_valid
  · exact c8FourRecordData408_valid
  · exact c8FourRecordData409_valid
  · exact c8FourRecordData410_valid
  · exact c8FourRecordData411_valid
  · exact c8FourRecordData412_valid
  · exact c8FourRecordData413_valid
  · exact c8FourRecordData414_valid
  · exact c8FourRecordData415_valid
  · exact c8FourRecordData416_valid
  · exact c8FourRecordData417_valid
  · exact c8FourRecordData418_valid
  · exact c8FourRecordData419_valid
  · exact c8FourRecordData420_valid
  · exact c8FourRecordData421_valid
  · exact c8FourRecordData422_valid
  · exact c8FourRecordData423_valid
  · exact c8FourRecordData424_valid
  · exact c8FourRecordData425_valid
  · exact c8FourRecordData426_valid
  · exact c8FourRecordData427_valid
  · exact c8FourRecordData428_valid
  · exact c8FourRecordData429_valid
  · exact c8FourRecordData430_valid
  · exact c8FourRecordData431_valid
  · exact c8FourRecordData432_valid
  · exact c8FourRecordData433_valid
  · exact c8FourRecordData434_valid
  · exact c8FourRecordData435_valid
  · exact c8FourRecordData436_valid
  · exact c8FourRecordData437_valid
  · exact c8FourRecordData438_valid
  · exact c8FourRecordData439_valid
  · exact c8FourRecordData440_valid
  · exact c8FourRecordData441_valid
  · exact c8FourRecordData442_valid
  · exact c8FourRecordData443_valid
  · exact c8FourRecordData444_valid
  · exact c8FourRecordData445_valid
  · exact c8FourRecordData446_valid
  · exact c8FourRecordData447_valid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk6_kernels (j : Fin 64) :
    c8FourKernelListsValid (c8FourRecordChunk6[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData384_kernels
  · exact c8FourRecordData385_kernels
  · exact c8FourRecordData386_kernels
  · exact c8FourRecordData387_kernels
  · exact c8FourRecordData388_kernels
  · exact c8FourRecordData389_kernels
  · exact c8FourRecordData390_kernels
  · exact c8FourRecordData391_kernels
  · exact c8FourRecordData392_kernels
  · exact c8FourRecordData393_kernels
  · exact c8FourRecordData394_kernels
  · exact c8FourRecordData395_kernels
  · exact c8FourRecordData396_kernels
  · exact c8FourRecordData397_kernels
  · exact c8FourRecordData398_kernels
  · exact c8FourRecordData399_kernels
  · exact c8FourRecordData400_kernels
  · exact c8FourRecordData401_kernels
  · exact c8FourRecordData402_kernels
  · exact c8FourRecordData403_kernels
  · exact c8FourRecordData404_kernels
  · exact c8FourRecordData405_kernels
  · exact c8FourRecordData406_kernels
  · exact c8FourRecordData407_kernels
  · exact c8FourRecordData408_kernels
  · exact c8FourRecordData409_kernels
  · exact c8FourRecordData410_kernels
  · exact c8FourRecordData411_kernels
  · exact c8FourRecordData412_kernels
  · exact c8FourRecordData413_kernels
  · exact c8FourRecordData414_kernels
  · exact c8FourRecordData415_kernels
  · exact c8FourRecordData416_kernels
  · exact c8FourRecordData417_kernels
  · exact c8FourRecordData418_kernels
  · exact c8FourRecordData419_kernels
  · exact c8FourRecordData420_kernels
  · exact c8FourRecordData421_kernels
  · exact c8FourRecordData422_kernels
  · exact c8FourRecordData423_kernels
  · exact c8FourRecordData424_kernels
  · exact c8FourRecordData425_kernels
  · exact c8FourRecordData426_kernels
  · exact c8FourRecordData427_kernels
  · exact c8FourRecordData428_kernels
  · exact c8FourRecordData429_kernels
  · exact c8FourRecordData430_kernels
  · exact c8FourRecordData431_kernels
  · exact c8FourRecordData432_kernels
  · exact c8FourRecordData433_kernels
  · exact c8FourRecordData434_kernels
  · exact c8FourRecordData435_kernels
  · exact c8FourRecordData436_kernels
  · exact c8FourRecordData437_kernels
  · exact c8FourRecordData438_kernels
  · exact c8FourRecordData439_kernels
  · exact c8FourRecordData440_kernels
  · exact c8FourRecordData441_kernels
  · exact c8FourRecordData442_kernels
  · exact c8FourRecordData443_kernels
  · exact c8FourRecordData444_kernels
  · exact c8FourRecordData445_kernels
  · exact c8FourRecordData446_kernels
  · exact c8FourRecordData447_kernels

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk6_vectors (j : Fin 64) :
    c8FourGeneratorVectorsValid (c8FourRecordChunk6[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData384_vectors
  · exact c8FourRecordData385_vectors
  · exact c8FourRecordData386_vectors
  · exact c8FourRecordData387_vectors
  · exact c8FourRecordData388_vectors
  · exact c8FourRecordData389_vectors
  · exact c8FourRecordData390_vectors
  · exact c8FourRecordData391_vectors
  · exact c8FourRecordData392_vectors
  · exact c8FourRecordData393_vectors
  · exact c8FourRecordData394_vectors
  · exact c8FourRecordData395_vectors
  · exact c8FourRecordData396_vectors
  · exact c8FourRecordData397_vectors
  · exact c8FourRecordData398_vectors
  · exact c8FourRecordData399_vectors
  · exact c8FourRecordData400_vectors
  · exact c8FourRecordData401_vectors
  · exact c8FourRecordData402_vectors
  · exact c8FourRecordData403_vectors
  · exact c8FourRecordData404_vectors
  · exact c8FourRecordData405_vectors
  · exact c8FourRecordData406_vectors
  · exact c8FourRecordData407_vectors
  · exact c8FourRecordData408_vectors
  · exact c8FourRecordData409_vectors
  · exact c8FourRecordData410_vectors
  · exact c8FourRecordData411_vectors
  · exact c8FourRecordData412_vectors
  · exact c8FourRecordData413_vectors
  · exact c8FourRecordData414_vectors
  · exact c8FourRecordData415_vectors
  · exact c8FourRecordData416_vectors
  · exact c8FourRecordData417_vectors
  · exact c8FourRecordData418_vectors
  · exact c8FourRecordData419_vectors
  · exact c8FourRecordData420_vectors
  · exact c8FourRecordData421_vectors
  · exact c8FourRecordData422_vectors
  · exact c8FourRecordData423_vectors
  · exact c8FourRecordData424_vectors
  · exact c8FourRecordData425_vectors
  · exact c8FourRecordData426_vectors
  · exact c8FourRecordData427_vectors
  · exact c8FourRecordData428_vectors
  · exact c8FourRecordData429_vectors
  · exact c8FourRecordData430_vectors
  · exact c8FourRecordData431_vectors
  · exact c8FourRecordData432_vectors
  · exact c8FourRecordData433_vectors
  · exact c8FourRecordData434_vectors
  · exact c8FourRecordData435_vectors
  · exact c8FourRecordData436_vectors
  · exact c8FourRecordData437_vectors
  · exact c8FourRecordData438_vectors
  · exact c8FourRecordData439_vectors
  · exact c8FourRecordData440_vectors
  · exact c8FourRecordData441_vectors
  · exact c8FourRecordData442_vectors
  · exact c8FourRecordData443_vectors
  · exact c8FourRecordData444_vectors
  · exact c8FourRecordData445_vectors
  · exact c8FourRecordData446_vectors
  · exact c8FourRecordData447_vectors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk6_rank_cards (j : Fin 64) :
    (c8FourRecordBinaryImages (c8FourRecordChunk6[j.val]!)).card = 2 ^ (c8FourRecordChunk6[j.val]!).generators.length := by
  fin_cases j
  · change (c8FourRecordBinaryImages c8FourRecordData384).card = 2 ^ c8FourRecordData384.generators.length
    rw [(c8FourRecordData384_rank_card).2]
    exact (c8FourRecordData384_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData385).card = 2 ^ c8FourRecordData385.generators.length
    rw [(c8FourRecordData385_rank_card).2]
    exact (c8FourRecordData385_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData386).card = 2 ^ c8FourRecordData386.generators.length
    rw [(c8FourRecordData386_rank_card).2]
    exact (c8FourRecordData386_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData387).card = 2 ^ c8FourRecordData387.generators.length
    rw [(c8FourRecordData387_rank_card).2]
    exact (c8FourRecordData387_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData388).card = 2 ^ c8FourRecordData388.generators.length
    rw [(c8FourRecordData388_rank_card).2]
    exact (c8FourRecordData388_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData389).card = 2 ^ c8FourRecordData389.generators.length
    rw [(c8FourRecordData389_rank_card).2]
    exact (c8FourRecordData389_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData390).card = 2 ^ c8FourRecordData390.generators.length
    rw [(c8FourRecordData390_rank_card).2]
    exact (c8FourRecordData390_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData391).card = 2 ^ c8FourRecordData391.generators.length
    rw [(c8FourRecordData391_rank_card).2]
    exact (c8FourRecordData391_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData392).card = 2 ^ c8FourRecordData392.generators.length
    rw [(c8FourRecordData392_rank_card).2]
    exact (c8FourRecordData392_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData393).card = 2 ^ c8FourRecordData393.generators.length
    rw [(c8FourRecordData393_rank_card).2]
    exact (c8FourRecordData393_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData394).card = 2 ^ c8FourRecordData394.generators.length
    rw [(c8FourRecordData394_rank_card).2]
    exact (c8FourRecordData394_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData395).card = 2 ^ c8FourRecordData395.generators.length
    rw [(c8FourRecordData395_rank_card).2]
    exact (c8FourRecordData395_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData396).card = 2 ^ c8FourRecordData396.generators.length
    rw [(c8FourRecordData396_rank_card).2]
    exact (c8FourRecordData396_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData397).card = 2 ^ c8FourRecordData397.generators.length
    rw [(c8FourRecordData397_rank_card).2]
    exact (c8FourRecordData397_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData398).card = 2 ^ c8FourRecordData398.generators.length
    rw [(c8FourRecordData398_rank_card).2]
    exact (c8FourRecordData398_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData399).card = 2 ^ c8FourRecordData399.generators.length
    rw [(c8FourRecordData399_rank_card).2]
    exact (c8FourRecordData399_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData400).card = 2 ^ c8FourRecordData400.generators.length
    rw [(c8FourRecordData400_rank_card).2]
    exact (c8FourRecordData400_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData401).card = 2 ^ c8FourRecordData401.generators.length
    rw [(c8FourRecordData401_rank_card).2]
    exact (c8FourRecordData401_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData402).card = 2 ^ c8FourRecordData402.generators.length
    rw [(c8FourRecordData402_rank_card).2]
    exact (c8FourRecordData402_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData403).card = 2 ^ c8FourRecordData403.generators.length
    rw [(c8FourRecordData403_rank_card).2]
    exact (c8FourRecordData403_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData404).card = 2 ^ c8FourRecordData404.generators.length
    rw [(c8FourRecordData404_rank_card).2]
    exact (c8FourRecordData404_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData405).card = 2 ^ c8FourRecordData405.generators.length
    rw [(c8FourRecordData405_rank_card).2]
    exact (c8FourRecordData405_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData406).card = 2 ^ c8FourRecordData406.generators.length
    rw [(c8FourRecordData406_rank_card).2]
    exact (c8FourRecordData406_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData407).card = 2 ^ c8FourRecordData407.generators.length
    rw [(c8FourRecordData407_rank_card).2]
    exact (c8FourRecordData407_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData408).card = 2 ^ c8FourRecordData408.generators.length
    rw [(c8FourRecordData408_rank_card).2]
    exact (c8FourRecordData408_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData409).card = 2 ^ c8FourRecordData409.generators.length
    rw [(c8FourRecordData409_rank_card).2]
    exact (c8FourRecordData409_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData410).card = 2 ^ c8FourRecordData410.generators.length
    rw [(c8FourRecordData410_rank_card).2]
    exact (c8FourRecordData410_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData411).card = 2 ^ c8FourRecordData411.generators.length
    rw [(c8FourRecordData411_rank_card).2]
    exact (c8FourRecordData411_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData412).card = 2 ^ c8FourRecordData412.generators.length
    rw [(c8FourRecordData412_rank_card).2]
    exact (c8FourRecordData412_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData413).card = 2 ^ c8FourRecordData413.generators.length
    rw [(c8FourRecordData413_rank_card).2]
    exact (c8FourRecordData413_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData414).card = 2 ^ c8FourRecordData414.generators.length
    rw [(c8FourRecordData414_rank_card).2]
    exact (c8FourRecordData414_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData415).card = 2 ^ c8FourRecordData415.generators.length
    rw [(c8FourRecordData415_rank_card).2]
    exact (c8FourRecordData415_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData416).card = 2 ^ c8FourRecordData416.generators.length
    rw [(c8FourRecordData416_rank_card).2]
    exact (c8FourRecordData416_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData417).card = 2 ^ c8FourRecordData417.generators.length
    rw [(c8FourRecordData417_rank_card).2]
    exact (c8FourRecordData417_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData418).card = 2 ^ c8FourRecordData418.generators.length
    rw [(c8FourRecordData418_rank_card).2]
    exact (c8FourRecordData418_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData419).card = 2 ^ c8FourRecordData419.generators.length
    rw [(c8FourRecordData419_rank_card).2]
    exact (c8FourRecordData419_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData420).card = 2 ^ c8FourRecordData420.generators.length
    rw [(c8FourRecordData420_rank_card).2]
    exact (c8FourRecordData420_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData421).card = 2 ^ c8FourRecordData421.generators.length
    rw [(c8FourRecordData421_rank_card).2]
    exact (c8FourRecordData421_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData422).card = 2 ^ c8FourRecordData422.generators.length
    rw [(c8FourRecordData422_rank_card).2]
    exact (c8FourRecordData422_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData423).card = 2 ^ c8FourRecordData423.generators.length
    rw [(c8FourRecordData423_rank_card).2]
    exact (c8FourRecordData423_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData424).card = 2 ^ c8FourRecordData424.generators.length
    rw [(c8FourRecordData424_rank_card).2]
    exact (c8FourRecordData424_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData425).card = 2 ^ c8FourRecordData425.generators.length
    rw [(c8FourRecordData425_rank_card).2]
    exact (c8FourRecordData425_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData426).card = 2 ^ c8FourRecordData426.generators.length
    rw [(c8FourRecordData426_rank_card).2]
    exact (c8FourRecordData426_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData427).card = 2 ^ c8FourRecordData427.generators.length
    rw [(c8FourRecordData427_rank_card).2]
    exact (c8FourRecordData427_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData428).card = 2 ^ c8FourRecordData428.generators.length
    rw [(c8FourRecordData428_rank_card).2]
    exact (c8FourRecordData428_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData429).card = 2 ^ c8FourRecordData429.generators.length
    rw [(c8FourRecordData429_rank_card).2]
    exact (c8FourRecordData429_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData430).card = 2 ^ c8FourRecordData430.generators.length
    rw [(c8FourRecordData430_rank_card).2]
    exact (c8FourRecordData430_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData431).card = 2 ^ c8FourRecordData431.generators.length
    rw [(c8FourRecordData431_rank_card).2]
    exact (c8FourRecordData431_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData432).card = 2 ^ c8FourRecordData432.generators.length
    rw [(c8FourRecordData432_rank_card).2]
    exact (c8FourRecordData432_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData433).card = 2 ^ c8FourRecordData433.generators.length
    rw [(c8FourRecordData433_rank_card).2]
    exact (c8FourRecordData433_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData434).card = 2 ^ c8FourRecordData434.generators.length
    rw [(c8FourRecordData434_rank_card).2]
    exact (c8FourRecordData434_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData435).card = 2 ^ c8FourRecordData435.generators.length
    rw [(c8FourRecordData435_rank_card).2]
    exact (c8FourRecordData435_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData436).card = 2 ^ c8FourRecordData436.generators.length
    rw [(c8FourRecordData436_rank_card).2]
    exact (c8FourRecordData436_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData437).card = 2 ^ c8FourRecordData437.generators.length
    rw [(c8FourRecordData437_rank_card).2]
    exact (c8FourRecordData437_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData438).card = 2 ^ c8FourRecordData438.generators.length
    rw [(c8FourRecordData438_rank_card).2]
    exact (c8FourRecordData438_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData439).card = 2 ^ c8FourRecordData439.generators.length
    rw [(c8FourRecordData439_rank_card).2]
    exact (c8FourRecordData439_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData440).card = 2 ^ c8FourRecordData440.generators.length
    rw [(c8FourRecordData440_rank_card).2]
    exact (c8FourRecordData440_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData441).card = 2 ^ c8FourRecordData441.generators.length
    rw [(c8FourRecordData441_rank_card).2]
    exact (c8FourRecordData441_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData442).card = 2 ^ c8FourRecordData442.generators.length
    rw [(c8FourRecordData442_rank_card).2]
    exact (c8FourRecordData442_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData443).card = 2 ^ c8FourRecordData443.generators.length
    rw [(c8FourRecordData443_rank_card).2]
    exact (c8FourRecordData443_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData444).card = 2 ^ c8FourRecordData444.generators.length
    rw [(c8FourRecordData444_rank_card).2]
    exact (c8FourRecordData444_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData445).card = 2 ^ c8FourRecordData445.generators.length
    rw [(c8FourRecordData445_rank_card).2]
    exact (c8FourRecordData445_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData446).card = 2 ^ c8FourRecordData446.generators.length
    rw [(c8FourRecordData446_rank_card).2]
    exact (c8FourRecordData446_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData447).card = 2 ^ c8FourRecordData447.generators.length
    rw [(c8FourRecordData447_rank_card).2]
    exact (c8FourRecordData447_rank_card).1

end CFSG.LargeEvenClassification.Helpers
