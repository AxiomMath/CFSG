module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupValid1
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupKernel1
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRank1

public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk1_valid (j : Fin 64) :
    c8FourRecordValid (c8FourRecordChunk1[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData64_valid
  · exact c8FourRecordData65_valid
  · exact c8FourRecordData66_valid
  · exact c8FourRecordData67_valid
  · exact c8FourRecordData68_valid
  · exact c8FourRecordData69_valid
  · exact c8FourRecordData70_valid
  · exact c8FourRecordData71_valid
  · exact c8FourRecordData72_valid
  · exact c8FourRecordData73_valid
  · exact c8FourRecordData74_valid
  · exact c8FourRecordData75_valid
  · exact c8FourRecordData76_valid
  · exact c8FourRecordData77_valid
  · exact c8FourRecordData78_valid
  · exact c8FourRecordData79_valid
  · exact c8FourRecordData80_valid
  · exact c8FourRecordData81_valid
  · exact c8FourRecordData82_valid
  · exact c8FourRecordData83_valid
  · exact c8FourRecordData84_valid
  · exact c8FourRecordData85_valid
  · exact c8FourRecordData86_valid
  · exact c8FourRecordData87_valid
  · exact c8FourRecordData88_valid
  · exact c8FourRecordData89_valid
  · exact c8FourRecordData90_valid
  · exact c8FourRecordData91_valid
  · exact c8FourRecordData92_valid
  · exact c8FourRecordData93_valid
  · exact c8FourRecordData94_valid
  · exact c8FourRecordData95_valid
  · exact c8FourRecordData96_valid
  · exact c8FourRecordData97_valid
  · exact c8FourRecordData98_valid
  · exact c8FourRecordData99_valid
  · exact c8FourRecordData100_valid
  · exact c8FourRecordData101_valid
  · exact c8FourRecordData102_valid
  · exact c8FourRecordData103_valid
  · exact c8FourRecordData104_valid
  · exact c8FourRecordData105_valid
  · exact c8FourRecordData106_valid
  · exact c8FourRecordData107_valid
  · exact c8FourRecordData108_valid
  · exact c8FourRecordData109_valid
  · exact c8FourRecordData110_valid
  · exact c8FourRecordData111_valid
  · exact c8FourRecordData112_valid
  · exact c8FourRecordData113_valid
  · exact c8FourRecordData114_valid
  · exact c8FourRecordData115_valid
  · exact c8FourRecordData116_valid
  · exact c8FourRecordData117_valid
  · exact c8FourRecordData118_valid
  · exact c8FourRecordData119_valid
  · exact c8FourRecordData120_valid
  · exact c8FourRecordData121_valid
  · exact c8FourRecordData122_valid
  · exact c8FourRecordData123_valid
  · exact c8FourRecordData124_valid
  · exact c8FourRecordData125_valid
  · exact c8FourRecordData126_valid
  · exact c8FourRecordData127_valid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk1_kernels (j : Fin 64) :
    c8FourKernelListsValid (c8FourRecordChunk1[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData64_kernels
  · exact c8FourRecordData65_kernels
  · exact c8FourRecordData66_kernels
  · exact c8FourRecordData67_kernels
  · exact c8FourRecordData68_kernels
  · exact c8FourRecordData69_kernels
  · exact c8FourRecordData70_kernels
  · exact c8FourRecordData71_kernels
  · exact c8FourRecordData72_kernels
  · exact c8FourRecordData73_kernels
  · exact c8FourRecordData74_kernels
  · exact c8FourRecordData75_kernels
  · exact c8FourRecordData76_kernels
  · exact c8FourRecordData77_kernels
  · exact c8FourRecordData78_kernels
  · exact c8FourRecordData79_kernels
  · exact c8FourRecordData80_kernels
  · exact c8FourRecordData81_kernels
  · exact c8FourRecordData82_kernels
  · exact c8FourRecordData83_kernels
  · exact c8FourRecordData84_kernels
  · exact c8FourRecordData85_kernels
  · exact c8FourRecordData86_kernels
  · exact c8FourRecordData87_kernels
  · exact c8FourRecordData88_kernels
  · exact c8FourRecordData89_kernels
  · exact c8FourRecordData90_kernels
  · exact c8FourRecordData91_kernels
  · exact c8FourRecordData92_kernels
  · exact c8FourRecordData93_kernels
  · exact c8FourRecordData94_kernels
  · exact c8FourRecordData95_kernels
  · exact c8FourRecordData96_kernels
  · exact c8FourRecordData97_kernels
  · exact c8FourRecordData98_kernels
  · exact c8FourRecordData99_kernels
  · exact c8FourRecordData100_kernels
  · exact c8FourRecordData101_kernels
  · exact c8FourRecordData102_kernels
  · exact c8FourRecordData103_kernels
  · exact c8FourRecordData104_kernels
  · exact c8FourRecordData105_kernels
  · exact c8FourRecordData106_kernels
  · exact c8FourRecordData107_kernels
  · exact c8FourRecordData108_kernels
  · exact c8FourRecordData109_kernels
  · exact c8FourRecordData110_kernels
  · exact c8FourRecordData111_kernels
  · exact c8FourRecordData112_kernels
  · exact c8FourRecordData113_kernels
  · exact c8FourRecordData114_kernels
  · exact c8FourRecordData115_kernels
  · exact c8FourRecordData116_kernels
  · exact c8FourRecordData117_kernels
  · exact c8FourRecordData118_kernels
  · exact c8FourRecordData119_kernels
  · exact c8FourRecordData120_kernels
  · exact c8FourRecordData121_kernels
  · exact c8FourRecordData122_kernels
  · exact c8FourRecordData123_kernels
  · exact c8FourRecordData124_kernels
  · exact c8FourRecordData125_kernels
  · exact c8FourRecordData126_kernels
  · exact c8FourRecordData127_kernels

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk1_vectors (j : Fin 64) :
    c8FourGeneratorVectorsValid (c8FourRecordChunk1[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData64_vectors
  · exact c8FourRecordData65_vectors
  · exact c8FourRecordData66_vectors
  · exact c8FourRecordData67_vectors
  · exact c8FourRecordData68_vectors
  · exact c8FourRecordData69_vectors
  · exact c8FourRecordData70_vectors
  · exact c8FourRecordData71_vectors
  · exact c8FourRecordData72_vectors
  · exact c8FourRecordData73_vectors
  · exact c8FourRecordData74_vectors
  · exact c8FourRecordData75_vectors
  · exact c8FourRecordData76_vectors
  · exact c8FourRecordData77_vectors
  · exact c8FourRecordData78_vectors
  · exact c8FourRecordData79_vectors
  · exact c8FourRecordData80_vectors
  · exact c8FourRecordData81_vectors
  · exact c8FourRecordData82_vectors
  · exact c8FourRecordData83_vectors
  · exact c8FourRecordData84_vectors
  · exact c8FourRecordData85_vectors
  · exact c8FourRecordData86_vectors
  · exact c8FourRecordData87_vectors
  · exact c8FourRecordData88_vectors
  · exact c8FourRecordData89_vectors
  · exact c8FourRecordData90_vectors
  · exact c8FourRecordData91_vectors
  · exact c8FourRecordData92_vectors
  · exact c8FourRecordData93_vectors
  · exact c8FourRecordData94_vectors
  · exact c8FourRecordData95_vectors
  · exact c8FourRecordData96_vectors
  · exact c8FourRecordData97_vectors
  · exact c8FourRecordData98_vectors
  · exact c8FourRecordData99_vectors
  · exact c8FourRecordData100_vectors
  · exact c8FourRecordData101_vectors
  · exact c8FourRecordData102_vectors
  · exact c8FourRecordData103_vectors
  · exact c8FourRecordData104_vectors
  · exact c8FourRecordData105_vectors
  · exact c8FourRecordData106_vectors
  · exact c8FourRecordData107_vectors
  · exact c8FourRecordData108_vectors
  · exact c8FourRecordData109_vectors
  · exact c8FourRecordData110_vectors
  · exact c8FourRecordData111_vectors
  · exact c8FourRecordData112_vectors
  · exact c8FourRecordData113_vectors
  · exact c8FourRecordData114_vectors
  · exact c8FourRecordData115_vectors
  · exact c8FourRecordData116_vectors
  · exact c8FourRecordData117_vectors
  · exact c8FourRecordData118_vectors
  · exact c8FourRecordData119_vectors
  · exact c8FourRecordData120_vectors
  · exact c8FourRecordData121_vectors
  · exact c8FourRecordData122_vectors
  · exact c8FourRecordData123_vectors
  · exact c8FourRecordData124_vectors
  · exact c8FourRecordData125_vectors
  · exact c8FourRecordData126_vectors
  · exact c8FourRecordData127_vectors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk1_rank_cards (j : Fin 64) :
    (c8FourRecordBinaryImages (c8FourRecordChunk1[j.val]!)).card = 2 ^ (c8FourRecordChunk1[j.val]!).generators.length := by
  fin_cases j
  · change (c8FourRecordBinaryImages c8FourRecordData64).card = 2 ^ c8FourRecordData64.generators.length
    rw [(c8FourRecordData64_rank_card).2]
    exact (c8FourRecordData64_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData65).card = 2 ^ c8FourRecordData65.generators.length
    rw [(c8FourRecordData65_rank_card).2]
    exact (c8FourRecordData65_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData66).card = 2 ^ c8FourRecordData66.generators.length
    rw [(c8FourRecordData66_rank_card).2]
    exact (c8FourRecordData66_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData67).card = 2 ^ c8FourRecordData67.generators.length
    rw [(c8FourRecordData67_rank_card).2]
    exact (c8FourRecordData67_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData68).card = 2 ^ c8FourRecordData68.generators.length
    rw [(c8FourRecordData68_rank_card).2]
    exact (c8FourRecordData68_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData69).card = 2 ^ c8FourRecordData69.generators.length
    rw [(c8FourRecordData69_rank_card).2]
    exact (c8FourRecordData69_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData70).card = 2 ^ c8FourRecordData70.generators.length
    rw [(c8FourRecordData70_rank_card).2]
    exact (c8FourRecordData70_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData71).card = 2 ^ c8FourRecordData71.generators.length
    rw [(c8FourRecordData71_rank_card).2]
    exact (c8FourRecordData71_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData72).card = 2 ^ c8FourRecordData72.generators.length
    rw [(c8FourRecordData72_rank_card).2]
    exact (c8FourRecordData72_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData73).card = 2 ^ c8FourRecordData73.generators.length
    rw [(c8FourRecordData73_rank_card).2]
    exact (c8FourRecordData73_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData74).card = 2 ^ c8FourRecordData74.generators.length
    rw [(c8FourRecordData74_rank_card).2]
    exact (c8FourRecordData74_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData75).card = 2 ^ c8FourRecordData75.generators.length
    rw [(c8FourRecordData75_rank_card).2]
    exact (c8FourRecordData75_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData76).card = 2 ^ c8FourRecordData76.generators.length
    rw [(c8FourRecordData76_rank_card).2]
    exact (c8FourRecordData76_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData77).card = 2 ^ c8FourRecordData77.generators.length
    rw [(c8FourRecordData77_rank_card).2]
    exact (c8FourRecordData77_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData78).card = 2 ^ c8FourRecordData78.generators.length
    rw [(c8FourRecordData78_rank_card).2]
    exact (c8FourRecordData78_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData79).card = 2 ^ c8FourRecordData79.generators.length
    rw [(c8FourRecordData79_rank_card).2]
    exact (c8FourRecordData79_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData80).card = 2 ^ c8FourRecordData80.generators.length
    rw [(c8FourRecordData80_rank_card).2]
    exact (c8FourRecordData80_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData81).card = 2 ^ c8FourRecordData81.generators.length
    rw [(c8FourRecordData81_rank_card).2]
    exact (c8FourRecordData81_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData82).card = 2 ^ c8FourRecordData82.generators.length
    rw [(c8FourRecordData82_rank_card).2]
    exact (c8FourRecordData82_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData83).card = 2 ^ c8FourRecordData83.generators.length
    rw [(c8FourRecordData83_rank_card).2]
    exact (c8FourRecordData83_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData84).card = 2 ^ c8FourRecordData84.generators.length
    rw [(c8FourRecordData84_rank_card).2]
    exact (c8FourRecordData84_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData85).card = 2 ^ c8FourRecordData85.generators.length
    rw [(c8FourRecordData85_rank_card).2]
    exact (c8FourRecordData85_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData86).card = 2 ^ c8FourRecordData86.generators.length
    rw [(c8FourRecordData86_rank_card).2]
    exact (c8FourRecordData86_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData87).card = 2 ^ c8FourRecordData87.generators.length
    rw [(c8FourRecordData87_rank_card).2]
    exact (c8FourRecordData87_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData88).card = 2 ^ c8FourRecordData88.generators.length
    rw [(c8FourRecordData88_rank_card).2]
    exact (c8FourRecordData88_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData89).card = 2 ^ c8FourRecordData89.generators.length
    rw [(c8FourRecordData89_rank_card).2]
    exact (c8FourRecordData89_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData90).card = 2 ^ c8FourRecordData90.generators.length
    rw [(c8FourRecordData90_rank_card).2]
    exact (c8FourRecordData90_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData91).card = 2 ^ c8FourRecordData91.generators.length
    rw [(c8FourRecordData91_rank_card).2]
    exact (c8FourRecordData91_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData92).card = 2 ^ c8FourRecordData92.generators.length
    rw [(c8FourRecordData92_rank_card).2]
    exact (c8FourRecordData92_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData93).card = 2 ^ c8FourRecordData93.generators.length
    rw [(c8FourRecordData93_rank_card).2]
    exact (c8FourRecordData93_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData94).card = 2 ^ c8FourRecordData94.generators.length
    rw [(c8FourRecordData94_rank_card).2]
    exact (c8FourRecordData94_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData95).card = 2 ^ c8FourRecordData95.generators.length
    rw [(c8FourRecordData95_rank_card).2]
    exact (c8FourRecordData95_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData96).card = 2 ^ c8FourRecordData96.generators.length
    rw [(c8FourRecordData96_rank_card).2]
    exact (c8FourRecordData96_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData97).card = 2 ^ c8FourRecordData97.generators.length
    rw [(c8FourRecordData97_rank_card).2]
    exact (c8FourRecordData97_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData98).card = 2 ^ c8FourRecordData98.generators.length
    rw [(c8FourRecordData98_rank_card).2]
    exact (c8FourRecordData98_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData99).card = 2 ^ c8FourRecordData99.generators.length
    rw [(c8FourRecordData99_rank_card).2]
    exact (c8FourRecordData99_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData100).card = 2 ^ c8FourRecordData100.generators.length
    rw [(c8FourRecordData100_rank_card).2]
    exact (c8FourRecordData100_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData101).card = 2 ^ c8FourRecordData101.generators.length
    rw [(c8FourRecordData101_rank_card).2]
    exact (c8FourRecordData101_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData102).card = 2 ^ c8FourRecordData102.generators.length
    rw [(c8FourRecordData102_rank_card).2]
    exact (c8FourRecordData102_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData103).card = 2 ^ c8FourRecordData103.generators.length
    rw [(c8FourRecordData103_rank_card).2]
    exact (c8FourRecordData103_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData104).card = 2 ^ c8FourRecordData104.generators.length
    rw [(c8FourRecordData104_rank_card).2]
    exact (c8FourRecordData104_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData105).card = 2 ^ c8FourRecordData105.generators.length
    rw [(c8FourRecordData105_rank_card).2]
    exact (c8FourRecordData105_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData106).card = 2 ^ c8FourRecordData106.generators.length
    rw [(c8FourRecordData106_rank_card).2]
    exact (c8FourRecordData106_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData107).card = 2 ^ c8FourRecordData107.generators.length
    rw [(c8FourRecordData107_rank_card).2]
    exact (c8FourRecordData107_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData108).card = 2 ^ c8FourRecordData108.generators.length
    rw [(c8FourRecordData108_rank_card).2]
    exact (c8FourRecordData108_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData109).card = 2 ^ c8FourRecordData109.generators.length
    rw [(c8FourRecordData109_rank_card).2]
    exact (c8FourRecordData109_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData110).card = 2 ^ c8FourRecordData110.generators.length
    rw [(c8FourRecordData110_rank_card).2]
    exact (c8FourRecordData110_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData111).card = 2 ^ c8FourRecordData111.generators.length
    rw [(c8FourRecordData111_rank_card).2]
    exact (c8FourRecordData111_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData112).card = 2 ^ c8FourRecordData112.generators.length
    rw [(c8FourRecordData112_rank_card).2]
    exact (c8FourRecordData112_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData113).card = 2 ^ c8FourRecordData113.generators.length
    rw [(c8FourRecordData113_rank_card).2]
    exact (c8FourRecordData113_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData114).card = 2 ^ c8FourRecordData114.generators.length
    rw [(c8FourRecordData114_rank_card).2]
    exact (c8FourRecordData114_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData115).card = 2 ^ c8FourRecordData115.generators.length
    rw [(c8FourRecordData115_rank_card).2]
    exact (c8FourRecordData115_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData116).card = 2 ^ c8FourRecordData116.generators.length
    rw [(c8FourRecordData116_rank_card).2]
    exact (c8FourRecordData116_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData117).card = 2 ^ c8FourRecordData117.generators.length
    rw [(c8FourRecordData117_rank_card).2]
    exact (c8FourRecordData117_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData118).card = 2 ^ c8FourRecordData118.generators.length
    rw [(c8FourRecordData118_rank_card).2]
    exact (c8FourRecordData118_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData119).card = 2 ^ c8FourRecordData119.generators.length
    rw [(c8FourRecordData119_rank_card).2]
    exact (c8FourRecordData119_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData120).card = 2 ^ c8FourRecordData120.generators.length
    rw [(c8FourRecordData120_rank_card).2]
    exact (c8FourRecordData120_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData121).card = 2 ^ c8FourRecordData121.generators.length
    rw [(c8FourRecordData121_rank_card).2]
    exact (c8FourRecordData121_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData122).card = 2 ^ c8FourRecordData122.generators.length
    rw [(c8FourRecordData122_rank_card).2]
    exact (c8FourRecordData122_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData123).card = 2 ^ c8FourRecordData123.generators.length
    rw [(c8FourRecordData123_rank_card).2]
    exact (c8FourRecordData123_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData124).card = 2 ^ c8FourRecordData124.generators.length
    rw [(c8FourRecordData124_rank_card).2]
    exact (c8FourRecordData124_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData125).card = 2 ^ c8FourRecordData125.generators.length
    rw [(c8FourRecordData125_rank_card).2]
    exact (c8FourRecordData125_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData126).card = 2 ^ c8FourRecordData126.generators.length
    rw [(c8FourRecordData126_rank_card).2]
    exact (c8FourRecordData126_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData127).card = 2 ^ c8FourRecordData127.generators.length
    rw [(c8FourRecordData127_rank_card).2]
    exact (c8FourRecordData127_rank_card).1

end CFSG.LargeEvenClassification.Helpers
