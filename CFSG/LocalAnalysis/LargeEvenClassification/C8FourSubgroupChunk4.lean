module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupValid4
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupKernel4
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRank4

public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk4_valid (j : Fin 64) :
    c8FourRecordValid (c8FourRecordChunk4[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData256_valid
  · exact c8FourRecordData257_valid
  · exact c8FourRecordData258_valid
  · exact c8FourRecordData259_valid
  · exact c8FourRecordData260_valid
  · exact c8FourRecordData261_valid
  · exact c8FourRecordData262_valid
  · exact c8FourRecordData263_valid
  · exact c8FourRecordData264_valid
  · exact c8FourRecordData265_valid
  · exact c8FourRecordData266_valid
  · exact c8FourRecordData267_valid
  · exact c8FourRecordData268_valid
  · exact c8FourRecordData269_valid
  · exact c8FourRecordData270_valid
  · exact c8FourRecordData271_valid
  · exact c8FourRecordData272_valid
  · exact c8FourRecordData273_valid
  · exact c8FourRecordData274_valid
  · exact c8FourRecordData275_valid
  · exact c8FourRecordData276_valid
  · exact c8FourRecordData277_valid
  · exact c8FourRecordData278_valid
  · exact c8FourRecordData279_valid
  · exact c8FourRecordData280_valid
  · exact c8FourRecordData281_valid
  · exact c8FourRecordData282_valid
  · exact c8FourRecordData283_valid
  · exact c8FourRecordData284_valid
  · exact c8FourRecordData285_valid
  · exact c8FourRecordData286_valid
  · exact c8FourRecordData287_valid
  · exact c8FourRecordData288_valid
  · exact c8FourRecordData289_valid
  · exact c8FourRecordData290_valid
  · exact c8FourRecordData291_valid
  · exact c8FourRecordData292_valid
  · exact c8FourRecordData293_valid
  · exact c8FourRecordData294_valid
  · exact c8FourRecordData295_valid
  · exact c8FourRecordData296_valid
  · exact c8FourRecordData297_valid
  · exact c8FourRecordData298_valid
  · exact c8FourRecordData299_valid
  · exact c8FourRecordData300_valid
  · exact c8FourRecordData301_valid
  · exact c8FourRecordData302_valid
  · exact c8FourRecordData303_valid
  · exact c8FourRecordData304_valid
  · exact c8FourRecordData305_valid
  · exact c8FourRecordData306_valid
  · exact c8FourRecordData307_valid
  · exact c8FourRecordData308_valid
  · exact c8FourRecordData309_valid
  · exact c8FourRecordData310_valid
  · exact c8FourRecordData311_valid
  · exact c8FourRecordData312_valid
  · exact c8FourRecordData313_valid
  · exact c8FourRecordData314_valid
  · exact c8FourRecordData315_valid
  · exact c8FourRecordData316_valid
  · exact c8FourRecordData317_valid
  · exact c8FourRecordData318_valid
  · exact c8FourRecordData319_valid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk4_kernels (j : Fin 64) :
    c8FourKernelListsValid (c8FourRecordChunk4[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData256_kernels
  · exact c8FourRecordData257_kernels
  · exact c8FourRecordData258_kernels
  · exact c8FourRecordData259_kernels
  · exact c8FourRecordData260_kernels
  · exact c8FourRecordData261_kernels
  · exact c8FourRecordData262_kernels
  · exact c8FourRecordData263_kernels
  · exact c8FourRecordData264_kernels
  · exact c8FourRecordData265_kernels
  · exact c8FourRecordData266_kernels
  · exact c8FourRecordData267_kernels
  · exact c8FourRecordData268_kernels
  · exact c8FourRecordData269_kernels
  · exact c8FourRecordData270_kernels
  · exact c8FourRecordData271_kernels
  · exact c8FourRecordData272_kernels
  · exact c8FourRecordData273_kernels
  · exact c8FourRecordData274_kernels
  · exact c8FourRecordData275_kernels
  · exact c8FourRecordData276_kernels
  · exact c8FourRecordData277_kernels
  · exact c8FourRecordData278_kernels
  · exact c8FourRecordData279_kernels
  · exact c8FourRecordData280_kernels
  · exact c8FourRecordData281_kernels
  · exact c8FourRecordData282_kernels
  · exact c8FourRecordData283_kernels
  · exact c8FourRecordData284_kernels
  · exact c8FourRecordData285_kernels
  · exact c8FourRecordData286_kernels
  · exact c8FourRecordData287_kernels
  · exact c8FourRecordData288_kernels
  · exact c8FourRecordData289_kernels
  · exact c8FourRecordData290_kernels
  · exact c8FourRecordData291_kernels
  · exact c8FourRecordData292_kernels
  · exact c8FourRecordData293_kernels
  · exact c8FourRecordData294_kernels
  · exact c8FourRecordData295_kernels
  · exact c8FourRecordData296_kernels
  · exact c8FourRecordData297_kernels
  · exact c8FourRecordData298_kernels
  · exact c8FourRecordData299_kernels
  · exact c8FourRecordData300_kernels
  · exact c8FourRecordData301_kernels
  · exact c8FourRecordData302_kernels
  · exact c8FourRecordData303_kernels
  · exact c8FourRecordData304_kernels
  · exact c8FourRecordData305_kernels
  · exact c8FourRecordData306_kernels
  · exact c8FourRecordData307_kernels
  · exact c8FourRecordData308_kernels
  · exact c8FourRecordData309_kernels
  · exact c8FourRecordData310_kernels
  · exact c8FourRecordData311_kernels
  · exact c8FourRecordData312_kernels
  · exact c8FourRecordData313_kernels
  · exact c8FourRecordData314_kernels
  · exact c8FourRecordData315_kernels
  · exact c8FourRecordData316_kernels
  · exact c8FourRecordData317_kernels
  · exact c8FourRecordData318_kernels
  · exact c8FourRecordData319_kernels

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk4_vectors (j : Fin 64) :
    c8FourGeneratorVectorsValid (c8FourRecordChunk4[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData256_vectors
  · exact c8FourRecordData257_vectors
  · exact c8FourRecordData258_vectors
  · exact c8FourRecordData259_vectors
  · exact c8FourRecordData260_vectors
  · exact c8FourRecordData261_vectors
  · exact c8FourRecordData262_vectors
  · exact c8FourRecordData263_vectors
  · exact c8FourRecordData264_vectors
  · exact c8FourRecordData265_vectors
  · exact c8FourRecordData266_vectors
  · exact c8FourRecordData267_vectors
  · exact c8FourRecordData268_vectors
  · exact c8FourRecordData269_vectors
  · exact c8FourRecordData270_vectors
  · exact c8FourRecordData271_vectors
  · exact c8FourRecordData272_vectors
  · exact c8FourRecordData273_vectors
  · exact c8FourRecordData274_vectors
  · exact c8FourRecordData275_vectors
  · exact c8FourRecordData276_vectors
  · exact c8FourRecordData277_vectors
  · exact c8FourRecordData278_vectors
  · exact c8FourRecordData279_vectors
  · exact c8FourRecordData280_vectors
  · exact c8FourRecordData281_vectors
  · exact c8FourRecordData282_vectors
  · exact c8FourRecordData283_vectors
  · exact c8FourRecordData284_vectors
  · exact c8FourRecordData285_vectors
  · exact c8FourRecordData286_vectors
  · exact c8FourRecordData287_vectors
  · exact c8FourRecordData288_vectors
  · exact c8FourRecordData289_vectors
  · exact c8FourRecordData290_vectors
  · exact c8FourRecordData291_vectors
  · exact c8FourRecordData292_vectors
  · exact c8FourRecordData293_vectors
  · exact c8FourRecordData294_vectors
  · exact c8FourRecordData295_vectors
  · exact c8FourRecordData296_vectors
  · exact c8FourRecordData297_vectors
  · exact c8FourRecordData298_vectors
  · exact c8FourRecordData299_vectors
  · exact c8FourRecordData300_vectors
  · exact c8FourRecordData301_vectors
  · exact c8FourRecordData302_vectors
  · exact c8FourRecordData303_vectors
  · exact c8FourRecordData304_vectors
  · exact c8FourRecordData305_vectors
  · exact c8FourRecordData306_vectors
  · exact c8FourRecordData307_vectors
  · exact c8FourRecordData308_vectors
  · exact c8FourRecordData309_vectors
  · exact c8FourRecordData310_vectors
  · exact c8FourRecordData311_vectors
  · exact c8FourRecordData312_vectors
  · exact c8FourRecordData313_vectors
  · exact c8FourRecordData314_vectors
  · exact c8FourRecordData315_vectors
  · exact c8FourRecordData316_vectors
  · exact c8FourRecordData317_vectors
  · exact c8FourRecordData318_vectors
  · exact c8FourRecordData319_vectors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk4_rank_cards (j : Fin 64) :
    (c8FourRecordBinaryImages (c8FourRecordChunk4[j.val]!)).card = 2 ^ (c8FourRecordChunk4[j.val]!).generators.length := by
  fin_cases j
  · change (c8FourRecordBinaryImages c8FourRecordData256).card = 2 ^ c8FourRecordData256.generators.length
    rw [(c8FourRecordData256_rank_card).2]
    exact (c8FourRecordData256_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData257).card = 2 ^ c8FourRecordData257.generators.length
    rw [(c8FourRecordData257_rank_card).2]
    exact (c8FourRecordData257_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData258).card = 2 ^ c8FourRecordData258.generators.length
    rw [(c8FourRecordData258_rank_card).2]
    exact (c8FourRecordData258_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData259).card = 2 ^ c8FourRecordData259.generators.length
    rw [(c8FourRecordData259_rank_card).2]
    exact (c8FourRecordData259_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData260).card = 2 ^ c8FourRecordData260.generators.length
    rw [(c8FourRecordData260_rank_card).2]
    exact (c8FourRecordData260_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData261).card = 2 ^ c8FourRecordData261.generators.length
    rw [(c8FourRecordData261_rank_card).2]
    exact (c8FourRecordData261_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData262).card = 2 ^ c8FourRecordData262.generators.length
    rw [(c8FourRecordData262_rank_card).2]
    exact (c8FourRecordData262_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData263).card = 2 ^ c8FourRecordData263.generators.length
    rw [(c8FourRecordData263_rank_card).2]
    exact (c8FourRecordData263_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData264).card = 2 ^ c8FourRecordData264.generators.length
    rw [(c8FourRecordData264_rank_card).2]
    exact (c8FourRecordData264_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData265).card = 2 ^ c8FourRecordData265.generators.length
    rw [(c8FourRecordData265_rank_card).2]
    exact (c8FourRecordData265_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData266).card = 2 ^ c8FourRecordData266.generators.length
    rw [(c8FourRecordData266_rank_card).2]
    exact (c8FourRecordData266_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData267).card = 2 ^ c8FourRecordData267.generators.length
    rw [(c8FourRecordData267_rank_card).2]
    exact (c8FourRecordData267_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData268).card = 2 ^ c8FourRecordData268.generators.length
    rw [(c8FourRecordData268_rank_card).2]
    exact (c8FourRecordData268_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData269).card = 2 ^ c8FourRecordData269.generators.length
    rw [(c8FourRecordData269_rank_card).2]
    exact (c8FourRecordData269_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData270).card = 2 ^ c8FourRecordData270.generators.length
    rw [(c8FourRecordData270_rank_card).2]
    exact (c8FourRecordData270_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData271).card = 2 ^ c8FourRecordData271.generators.length
    rw [(c8FourRecordData271_rank_card).2]
    exact (c8FourRecordData271_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData272).card = 2 ^ c8FourRecordData272.generators.length
    rw [(c8FourRecordData272_rank_card).2]
    exact (c8FourRecordData272_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData273).card = 2 ^ c8FourRecordData273.generators.length
    rw [(c8FourRecordData273_rank_card).2]
    exact (c8FourRecordData273_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData274).card = 2 ^ c8FourRecordData274.generators.length
    rw [(c8FourRecordData274_rank_card).2]
    exact (c8FourRecordData274_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData275).card = 2 ^ c8FourRecordData275.generators.length
    rw [(c8FourRecordData275_rank_card).2]
    exact (c8FourRecordData275_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData276).card = 2 ^ c8FourRecordData276.generators.length
    rw [(c8FourRecordData276_rank_card).2]
    exact (c8FourRecordData276_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData277).card = 2 ^ c8FourRecordData277.generators.length
    rw [(c8FourRecordData277_rank_card).2]
    exact (c8FourRecordData277_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData278).card = 2 ^ c8FourRecordData278.generators.length
    rw [(c8FourRecordData278_rank_card).2]
    exact (c8FourRecordData278_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData279).card = 2 ^ c8FourRecordData279.generators.length
    rw [(c8FourRecordData279_rank_card).2]
    exact (c8FourRecordData279_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData280).card = 2 ^ c8FourRecordData280.generators.length
    rw [(c8FourRecordData280_rank_card).2]
    exact (c8FourRecordData280_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData281).card = 2 ^ c8FourRecordData281.generators.length
    rw [(c8FourRecordData281_rank_card).2]
    exact (c8FourRecordData281_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData282).card = 2 ^ c8FourRecordData282.generators.length
    rw [(c8FourRecordData282_rank_card).2]
    exact (c8FourRecordData282_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData283).card = 2 ^ c8FourRecordData283.generators.length
    rw [(c8FourRecordData283_rank_card).2]
    exact (c8FourRecordData283_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData284).card = 2 ^ c8FourRecordData284.generators.length
    rw [(c8FourRecordData284_rank_card).2]
    exact (c8FourRecordData284_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData285).card = 2 ^ c8FourRecordData285.generators.length
    rw [(c8FourRecordData285_rank_card).2]
    exact (c8FourRecordData285_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData286).card = 2 ^ c8FourRecordData286.generators.length
    rw [(c8FourRecordData286_rank_card).2]
    exact (c8FourRecordData286_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData287).card = 2 ^ c8FourRecordData287.generators.length
    rw [(c8FourRecordData287_rank_card).2]
    exact (c8FourRecordData287_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData288).card = 2 ^ c8FourRecordData288.generators.length
    rw [(c8FourRecordData288_rank_card).2]
    exact (c8FourRecordData288_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData289).card = 2 ^ c8FourRecordData289.generators.length
    rw [(c8FourRecordData289_rank_card).2]
    exact (c8FourRecordData289_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData290).card = 2 ^ c8FourRecordData290.generators.length
    rw [(c8FourRecordData290_rank_card).2]
    exact (c8FourRecordData290_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData291).card = 2 ^ c8FourRecordData291.generators.length
    rw [(c8FourRecordData291_rank_card).2]
    exact (c8FourRecordData291_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData292).card = 2 ^ c8FourRecordData292.generators.length
    rw [(c8FourRecordData292_rank_card).2]
    exact (c8FourRecordData292_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData293).card = 2 ^ c8FourRecordData293.generators.length
    rw [(c8FourRecordData293_rank_card).2]
    exact (c8FourRecordData293_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData294).card = 2 ^ c8FourRecordData294.generators.length
    rw [(c8FourRecordData294_rank_card).2]
    exact (c8FourRecordData294_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData295).card = 2 ^ c8FourRecordData295.generators.length
    rw [(c8FourRecordData295_rank_card).2]
    exact (c8FourRecordData295_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData296).card = 2 ^ c8FourRecordData296.generators.length
    rw [(c8FourRecordData296_rank_card).2]
    exact (c8FourRecordData296_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData297).card = 2 ^ c8FourRecordData297.generators.length
    rw [(c8FourRecordData297_rank_card).2]
    exact (c8FourRecordData297_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData298).card = 2 ^ c8FourRecordData298.generators.length
    rw [(c8FourRecordData298_rank_card).2]
    exact (c8FourRecordData298_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData299).card = 2 ^ c8FourRecordData299.generators.length
    rw [(c8FourRecordData299_rank_card).2]
    exact (c8FourRecordData299_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData300).card = 2 ^ c8FourRecordData300.generators.length
    rw [(c8FourRecordData300_rank_card).2]
    exact (c8FourRecordData300_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData301).card = 2 ^ c8FourRecordData301.generators.length
    rw [(c8FourRecordData301_rank_card).2]
    exact (c8FourRecordData301_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData302).card = 2 ^ c8FourRecordData302.generators.length
    rw [(c8FourRecordData302_rank_card).2]
    exact (c8FourRecordData302_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData303).card = 2 ^ c8FourRecordData303.generators.length
    rw [(c8FourRecordData303_rank_card).2]
    exact (c8FourRecordData303_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData304).card = 2 ^ c8FourRecordData304.generators.length
    rw [(c8FourRecordData304_rank_card).2]
    exact (c8FourRecordData304_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData305).card = 2 ^ c8FourRecordData305.generators.length
    rw [(c8FourRecordData305_rank_card).2]
    exact (c8FourRecordData305_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData306).card = 2 ^ c8FourRecordData306.generators.length
    rw [(c8FourRecordData306_rank_card).2]
    exact (c8FourRecordData306_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData307).card = 2 ^ c8FourRecordData307.generators.length
    rw [(c8FourRecordData307_rank_card).2]
    exact (c8FourRecordData307_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData308).card = 2 ^ c8FourRecordData308.generators.length
    rw [(c8FourRecordData308_rank_card).2]
    exact (c8FourRecordData308_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData309).card = 2 ^ c8FourRecordData309.generators.length
    rw [(c8FourRecordData309_rank_card).2]
    exact (c8FourRecordData309_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData310).card = 2 ^ c8FourRecordData310.generators.length
    rw [(c8FourRecordData310_rank_card).2]
    exact (c8FourRecordData310_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData311).card = 2 ^ c8FourRecordData311.generators.length
    rw [(c8FourRecordData311_rank_card).2]
    exact (c8FourRecordData311_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData312).card = 2 ^ c8FourRecordData312.generators.length
    rw [(c8FourRecordData312_rank_card).2]
    exact (c8FourRecordData312_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData313).card = 2 ^ c8FourRecordData313.generators.length
    rw [(c8FourRecordData313_rank_card).2]
    exact (c8FourRecordData313_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData314).card = 2 ^ c8FourRecordData314.generators.length
    rw [(c8FourRecordData314_rank_card).2]
    exact (c8FourRecordData314_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData315).card = 2 ^ c8FourRecordData315.generators.length
    rw [(c8FourRecordData315_rank_card).2]
    exact (c8FourRecordData315_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData316).card = 2 ^ c8FourRecordData316.generators.length
    rw [(c8FourRecordData316_rank_card).2]
    exact (c8FourRecordData316_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData317).card = 2 ^ c8FourRecordData317.generators.length
    rw [(c8FourRecordData317_rank_card).2]
    exact (c8FourRecordData317_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData318).card = 2 ^ c8FourRecordData318.generators.length
    rw [(c8FourRecordData318_rank_card).2]
    exact (c8FourRecordData318_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData319).card = 2 ^ c8FourRecordData319.generators.length
    rw [(c8FourRecordData319_rank_card).2]
    exact (c8FourRecordData319_rank_card).1

end CFSG.LargeEvenClassification.Helpers
