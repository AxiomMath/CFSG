module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupValid0
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupKernel0
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRank0

public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk0_valid (j : Fin 64) :
    c8FourRecordValid (c8FourRecordChunk0[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData0_valid
  · exact c8FourRecordData1_valid
  · exact c8FourRecordData2_valid
  · exact c8FourRecordData3_valid
  · exact c8FourRecordData4_valid
  · exact c8FourRecordData5_valid
  · exact c8FourRecordData6_valid
  · exact c8FourRecordData7_valid
  · exact c8FourRecordData8_valid
  · exact c8FourRecordData9_valid
  · exact c8FourRecordData10_valid
  · exact c8FourRecordData11_valid
  · exact c8FourRecordData12_valid
  · exact c8FourRecordData13_valid
  · exact c8FourRecordData14_valid
  · exact c8FourRecordData15_valid
  · exact c8FourRecordData16_valid
  · exact c8FourRecordData17_valid
  · exact c8FourRecordData18_valid
  · exact c8FourRecordData19_valid
  · exact c8FourRecordData20_valid
  · exact c8FourRecordData21_valid
  · exact c8FourRecordData22_valid
  · exact c8FourRecordData23_valid
  · exact c8FourRecordData24_valid
  · exact c8FourRecordData25_valid
  · exact c8FourRecordData26_valid
  · exact c8FourRecordData27_valid
  · exact c8FourRecordData28_valid
  · exact c8FourRecordData29_valid
  · exact c8FourRecordData30_valid
  · exact c8FourRecordData31_valid
  · exact c8FourRecordData32_valid
  · exact c8FourRecordData33_valid
  · exact c8FourRecordData34_valid
  · exact c8FourRecordData35_valid
  · exact c8FourRecordData36_valid
  · exact c8FourRecordData37_valid
  · exact c8FourRecordData38_valid
  · exact c8FourRecordData39_valid
  · exact c8FourRecordData40_valid
  · exact c8FourRecordData41_valid
  · exact c8FourRecordData42_valid
  · exact c8FourRecordData43_valid
  · exact c8FourRecordData44_valid
  · exact c8FourRecordData45_valid
  · exact c8FourRecordData46_valid
  · exact c8FourRecordData47_valid
  · exact c8FourRecordData48_valid
  · exact c8FourRecordData49_valid
  · exact c8FourRecordData50_valid
  · exact c8FourRecordData51_valid
  · exact c8FourRecordData52_valid
  · exact c8FourRecordData53_valid
  · exact c8FourRecordData54_valid
  · exact c8FourRecordData55_valid
  · exact c8FourRecordData56_valid
  · exact c8FourRecordData57_valid
  · exact c8FourRecordData58_valid
  · exact c8FourRecordData59_valid
  · exact c8FourRecordData60_valid
  · exact c8FourRecordData61_valid
  · exact c8FourRecordData62_valid
  · exact c8FourRecordData63_valid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk0_kernels (j : Fin 64) :
    c8FourKernelListsValid (c8FourRecordChunk0[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData0_kernels
  · exact c8FourRecordData1_kernels
  · exact c8FourRecordData2_kernels
  · exact c8FourRecordData3_kernels
  · exact c8FourRecordData4_kernels
  · exact c8FourRecordData5_kernels
  · exact c8FourRecordData6_kernels
  · exact c8FourRecordData7_kernels
  · exact c8FourRecordData8_kernels
  · exact c8FourRecordData9_kernels
  · exact c8FourRecordData10_kernels
  · exact c8FourRecordData11_kernels
  · exact c8FourRecordData12_kernels
  · exact c8FourRecordData13_kernels
  · exact c8FourRecordData14_kernels
  · exact c8FourRecordData15_kernels
  · exact c8FourRecordData16_kernels
  · exact c8FourRecordData17_kernels
  · exact c8FourRecordData18_kernels
  · exact c8FourRecordData19_kernels
  · exact c8FourRecordData20_kernels
  · exact c8FourRecordData21_kernels
  · exact c8FourRecordData22_kernels
  · exact c8FourRecordData23_kernels
  · exact c8FourRecordData24_kernels
  · exact c8FourRecordData25_kernels
  · exact c8FourRecordData26_kernels
  · exact c8FourRecordData27_kernels
  · exact c8FourRecordData28_kernels
  · exact c8FourRecordData29_kernels
  · exact c8FourRecordData30_kernels
  · exact c8FourRecordData31_kernels
  · exact c8FourRecordData32_kernels
  · exact c8FourRecordData33_kernels
  · exact c8FourRecordData34_kernels
  · exact c8FourRecordData35_kernels
  · exact c8FourRecordData36_kernels
  · exact c8FourRecordData37_kernels
  · exact c8FourRecordData38_kernels
  · exact c8FourRecordData39_kernels
  · exact c8FourRecordData40_kernels
  · exact c8FourRecordData41_kernels
  · exact c8FourRecordData42_kernels
  · exact c8FourRecordData43_kernels
  · exact c8FourRecordData44_kernels
  · exact c8FourRecordData45_kernels
  · exact c8FourRecordData46_kernels
  · exact c8FourRecordData47_kernels
  · exact c8FourRecordData48_kernels
  · exact c8FourRecordData49_kernels
  · exact c8FourRecordData50_kernels
  · exact c8FourRecordData51_kernels
  · exact c8FourRecordData52_kernels
  · exact c8FourRecordData53_kernels
  · exact c8FourRecordData54_kernels
  · exact c8FourRecordData55_kernels
  · exact c8FourRecordData56_kernels
  · exact c8FourRecordData57_kernels
  · exact c8FourRecordData58_kernels
  · exact c8FourRecordData59_kernels
  · exact c8FourRecordData60_kernels
  · exact c8FourRecordData61_kernels
  · exact c8FourRecordData62_kernels
  · exact c8FourRecordData63_kernels

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk0_vectors (j : Fin 64) :
    c8FourGeneratorVectorsValid (c8FourRecordChunk0[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData0_vectors
  · exact c8FourRecordData1_vectors
  · exact c8FourRecordData2_vectors
  · exact c8FourRecordData3_vectors
  · exact c8FourRecordData4_vectors
  · exact c8FourRecordData5_vectors
  · exact c8FourRecordData6_vectors
  · exact c8FourRecordData7_vectors
  · exact c8FourRecordData8_vectors
  · exact c8FourRecordData9_vectors
  · exact c8FourRecordData10_vectors
  · exact c8FourRecordData11_vectors
  · exact c8FourRecordData12_vectors
  · exact c8FourRecordData13_vectors
  · exact c8FourRecordData14_vectors
  · exact c8FourRecordData15_vectors
  · exact c8FourRecordData16_vectors
  · exact c8FourRecordData17_vectors
  · exact c8FourRecordData18_vectors
  · exact c8FourRecordData19_vectors
  · exact c8FourRecordData20_vectors
  · exact c8FourRecordData21_vectors
  · exact c8FourRecordData22_vectors
  · exact c8FourRecordData23_vectors
  · exact c8FourRecordData24_vectors
  · exact c8FourRecordData25_vectors
  · exact c8FourRecordData26_vectors
  · exact c8FourRecordData27_vectors
  · exact c8FourRecordData28_vectors
  · exact c8FourRecordData29_vectors
  · exact c8FourRecordData30_vectors
  · exact c8FourRecordData31_vectors
  · exact c8FourRecordData32_vectors
  · exact c8FourRecordData33_vectors
  · exact c8FourRecordData34_vectors
  · exact c8FourRecordData35_vectors
  · exact c8FourRecordData36_vectors
  · exact c8FourRecordData37_vectors
  · exact c8FourRecordData38_vectors
  · exact c8FourRecordData39_vectors
  · exact c8FourRecordData40_vectors
  · exact c8FourRecordData41_vectors
  · exact c8FourRecordData42_vectors
  · exact c8FourRecordData43_vectors
  · exact c8FourRecordData44_vectors
  · exact c8FourRecordData45_vectors
  · exact c8FourRecordData46_vectors
  · exact c8FourRecordData47_vectors
  · exact c8FourRecordData48_vectors
  · exact c8FourRecordData49_vectors
  · exact c8FourRecordData50_vectors
  · exact c8FourRecordData51_vectors
  · exact c8FourRecordData52_vectors
  · exact c8FourRecordData53_vectors
  · exact c8FourRecordData54_vectors
  · exact c8FourRecordData55_vectors
  · exact c8FourRecordData56_vectors
  · exact c8FourRecordData57_vectors
  · exact c8FourRecordData58_vectors
  · exact c8FourRecordData59_vectors
  · exact c8FourRecordData60_vectors
  · exact c8FourRecordData61_vectors
  · exact c8FourRecordData62_vectors
  · exact c8FourRecordData63_vectors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk0_rank_cards (j : Fin 64) :
    (c8FourRecordBinaryImages (c8FourRecordChunk0[j.val]!)).card = 2 ^ (c8FourRecordChunk0[j.val]!).generators.length := by
  fin_cases j
  · change (c8FourRecordBinaryImages c8FourRecordData0).card = 2 ^ c8FourRecordData0.generators.length
    rw [(c8FourRecordData0_rank_card).2]
    exact (c8FourRecordData0_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData1).card = 2 ^ c8FourRecordData1.generators.length
    rw [(c8FourRecordData1_rank_card).2]
    exact (c8FourRecordData1_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData2).card = 2 ^ c8FourRecordData2.generators.length
    rw [(c8FourRecordData2_rank_card).2]
    exact (c8FourRecordData2_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData3).card = 2 ^ c8FourRecordData3.generators.length
    rw [(c8FourRecordData3_rank_card).2]
    exact (c8FourRecordData3_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData4).card = 2 ^ c8FourRecordData4.generators.length
    rw [(c8FourRecordData4_rank_card).2]
    exact (c8FourRecordData4_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData5).card = 2 ^ c8FourRecordData5.generators.length
    rw [(c8FourRecordData5_rank_card).2]
    exact (c8FourRecordData5_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData6).card = 2 ^ c8FourRecordData6.generators.length
    rw [(c8FourRecordData6_rank_card).2]
    exact (c8FourRecordData6_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData7).card = 2 ^ c8FourRecordData7.generators.length
    rw [(c8FourRecordData7_rank_card).2]
    exact (c8FourRecordData7_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData8).card = 2 ^ c8FourRecordData8.generators.length
    rw [(c8FourRecordData8_rank_card).2]
    exact (c8FourRecordData8_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData9).card = 2 ^ c8FourRecordData9.generators.length
    rw [(c8FourRecordData9_rank_card).2]
    exact (c8FourRecordData9_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData10).card = 2 ^ c8FourRecordData10.generators.length
    rw [(c8FourRecordData10_rank_card).2]
    exact (c8FourRecordData10_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData11).card = 2 ^ c8FourRecordData11.generators.length
    rw [(c8FourRecordData11_rank_card).2]
    exact (c8FourRecordData11_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData12).card = 2 ^ c8FourRecordData12.generators.length
    rw [(c8FourRecordData12_rank_card).2]
    exact (c8FourRecordData12_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData13).card = 2 ^ c8FourRecordData13.generators.length
    rw [(c8FourRecordData13_rank_card).2]
    exact (c8FourRecordData13_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData14).card = 2 ^ c8FourRecordData14.generators.length
    rw [(c8FourRecordData14_rank_card).2]
    exact (c8FourRecordData14_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData15).card = 2 ^ c8FourRecordData15.generators.length
    rw [(c8FourRecordData15_rank_card).2]
    exact (c8FourRecordData15_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData16).card = 2 ^ c8FourRecordData16.generators.length
    rw [(c8FourRecordData16_rank_card).2]
    exact (c8FourRecordData16_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData17).card = 2 ^ c8FourRecordData17.generators.length
    rw [(c8FourRecordData17_rank_card).2]
    exact (c8FourRecordData17_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData18).card = 2 ^ c8FourRecordData18.generators.length
    rw [(c8FourRecordData18_rank_card).2]
    exact (c8FourRecordData18_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData19).card = 2 ^ c8FourRecordData19.generators.length
    rw [(c8FourRecordData19_rank_card).2]
    exact (c8FourRecordData19_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData20).card = 2 ^ c8FourRecordData20.generators.length
    rw [(c8FourRecordData20_rank_card).2]
    exact (c8FourRecordData20_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData21).card = 2 ^ c8FourRecordData21.generators.length
    rw [(c8FourRecordData21_rank_card).2]
    exact (c8FourRecordData21_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData22).card = 2 ^ c8FourRecordData22.generators.length
    rw [(c8FourRecordData22_rank_card).2]
    exact (c8FourRecordData22_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData23).card = 2 ^ c8FourRecordData23.generators.length
    rw [(c8FourRecordData23_rank_card).2]
    exact (c8FourRecordData23_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData24).card = 2 ^ c8FourRecordData24.generators.length
    rw [(c8FourRecordData24_rank_card).2]
    exact (c8FourRecordData24_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData25).card = 2 ^ c8FourRecordData25.generators.length
    rw [(c8FourRecordData25_rank_card).2]
    exact (c8FourRecordData25_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData26).card = 2 ^ c8FourRecordData26.generators.length
    rw [(c8FourRecordData26_rank_card).2]
    exact (c8FourRecordData26_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData27).card = 2 ^ c8FourRecordData27.generators.length
    rw [(c8FourRecordData27_rank_card).2]
    exact (c8FourRecordData27_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData28).card = 2 ^ c8FourRecordData28.generators.length
    rw [(c8FourRecordData28_rank_card).2]
    exact (c8FourRecordData28_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData29).card = 2 ^ c8FourRecordData29.generators.length
    rw [(c8FourRecordData29_rank_card).2]
    exact (c8FourRecordData29_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData30).card = 2 ^ c8FourRecordData30.generators.length
    rw [(c8FourRecordData30_rank_card).2]
    exact (c8FourRecordData30_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData31).card = 2 ^ c8FourRecordData31.generators.length
    rw [(c8FourRecordData31_rank_card).2]
    exact (c8FourRecordData31_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData32).card = 2 ^ c8FourRecordData32.generators.length
    rw [(c8FourRecordData32_rank_card).2]
    exact (c8FourRecordData32_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData33).card = 2 ^ c8FourRecordData33.generators.length
    rw [(c8FourRecordData33_rank_card).2]
    exact (c8FourRecordData33_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData34).card = 2 ^ c8FourRecordData34.generators.length
    rw [(c8FourRecordData34_rank_card).2]
    exact (c8FourRecordData34_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData35).card = 2 ^ c8FourRecordData35.generators.length
    rw [(c8FourRecordData35_rank_card).2]
    exact (c8FourRecordData35_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData36).card = 2 ^ c8FourRecordData36.generators.length
    rw [(c8FourRecordData36_rank_card).2]
    exact (c8FourRecordData36_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData37).card = 2 ^ c8FourRecordData37.generators.length
    rw [(c8FourRecordData37_rank_card).2]
    exact (c8FourRecordData37_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData38).card = 2 ^ c8FourRecordData38.generators.length
    rw [(c8FourRecordData38_rank_card).2]
    exact (c8FourRecordData38_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData39).card = 2 ^ c8FourRecordData39.generators.length
    rw [(c8FourRecordData39_rank_card).2]
    exact (c8FourRecordData39_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData40).card = 2 ^ c8FourRecordData40.generators.length
    rw [(c8FourRecordData40_rank_card).2]
    exact (c8FourRecordData40_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData41).card = 2 ^ c8FourRecordData41.generators.length
    rw [(c8FourRecordData41_rank_card).2]
    exact (c8FourRecordData41_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData42).card = 2 ^ c8FourRecordData42.generators.length
    rw [(c8FourRecordData42_rank_card).2]
    exact (c8FourRecordData42_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData43).card = 2 ^ c8FourRecordData43.generators.length
    rw [(c8FourRecordData43_rank_card).2]
    exact (c8FourRecordData43_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData44).card = 2 ^ c8FourRecordData44.generators.length
    rw [(c8FourRecordData44_rank_card).2]
    exact (c8FourRecordData44_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData45).card = 2 ^ c8FourRecordData45.generators.length
    rw [(c8FourRecordData45_rank_card).2]
    exact (c8FourRecordData45_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData46).card = 2 ^ c8FourRecordData46.generators.length
    rw [(c8FourRecordData46_rank_card).2]
    exact (c8FourRecordData46_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData47).card = 2 ^ c8FourRecordData47.generators.length
    rw [(c8FourRecordData47_rank_card).2]
    exact (c8FourRecordData47_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData48).card = 2 ^ c8FourRecordData48.generators.length
    rw [(c8FourRecordData48_rank_card).2]
    exact (c8FourRecordData48_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData49).card = 2 ^ c8FourRecordData49.generators.length
    rw [(c8FourRecordData49_rank_card).2]
    exact (c8FourRecordData49_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData50).card = 2 ^ c8FourRecordData50.generators.length
    rw [(c8FourRecordData50_rank_card).2]
    exact (c8FourRecordData50_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData51).card = 2 ^ c8FourRecordData51.generators.length
    rw [(c8FourRecordData51_rank_card).2]
    exact (c8FourRecordData51_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData52).card = 2 ^ c8FourRecordData52.generators.length
    rw [(c8FourRecordData52_rank_card).2]
    exact (c8FourRecordData52_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData53).card = 2 ^ c8FourRecordData53.generators.length
    rw [(c8FourRecordData53_rank_card).2]
    exact (c8FourRecordData53_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData54).card = 2 ^ c8FourRecordData54.generators.length
    rw [(c8FourRecordData54_rank_card).2]
    exact (c8FourRecordData54_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData55).card = 2 ^ c8FourRecordData55.generators.length
    rw [(c8FourRecordData55_rank_card).2]
    exact (c8FourRecordData55_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData56).card = 2 ^ c8FourRecordData56.generators.length
    rw [(c8FourRecordData56_rank_card).2]
    exact (c8FourRecordData56_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData57).card = 2 ^ c8FourRecordData57.generators.length
    rw [(c8FourRecordData57_rank_card).2]
    exact (c8FourRecordData57_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData58).card = 2 ^ c8FourRecordData58.generators.length
    rw [(c8FourRecordData58_rank_card).2]
    exact (c8FourRecordData58_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData59).card = 2 ^ c8FourRecordData59.generators.length
    rw [(c8FourRecordData59_rank_card).2]
    exact (c8FourRecordData59_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData60).card = 2 ^ c8FourRecordData60.generators.length
    rw [(c8FourRecordData60_rank_card).2]
    exact (c8FourRecordData60_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData61).card = 2 ^ c8FourRecordData61.generators.length
    rw [(c8FourRecordData61_rank_card).2]
    exact (c8FourRecordData61_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData62).card = 2 ^ c8FourRecordData62.generators.length
    rw [(c8FourRecordData62_rank_card).2]
    exact (c8FourRecordData62_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData63).card = 2 ^ c8FourRecordData63.generators.length
    rw [(c8FourRecordData63_rank_card).2]
    exact (c8FourRecordData63_rank_card).1

end CFSG.LargeEvenClassification.Helpers
