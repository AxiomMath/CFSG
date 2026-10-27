module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupValid2
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupKernel2
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRank2

public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk2_valid (j : Fin 64) :
    c8FourRecordValid (c8FourRecordChunk2[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData128_valid
  · exact c8FourRecordData129_valid
  · exact c8FourRecordData130_valid
  · exact c8FourRecordData131_valid
  · exact c8FourRecordData132_valid
  · exact c8FourRecordData133_valid
  · exact c8FourRecordData134_valid
  · exact c8FourRecordData135_valid
  · exact c8FourRecordData136_valid
  · exact c8FourRecordData137_valid
  · exact c8FourRecordData138_valid
  · exact c8FourRecordData139_valid
  · exact c8FourRecordData140_valid
  · exact c8FourRecordData141_valid
  · exact c8FourRecordData142_valid
  · exact c8FourRecordData143_valid
  · exact c8FourRecordData144_valid
  · exact c8FourRecordData145_valid
  · exact c8FourRecordData146_valid
  · exact c8FourRecordData147_valid
  · exact c8FourRecordData148_valid
  · exact c8FourRecordData149_valid
  · exact c8FourRecordData150_valid
  · exact c8FourRecordData151_valid
  · exact c8FourRecordData152_valid
  · exact c8FourRecordData153_valid
  · exact c8FourRecordData154_valid
  · exact c8FourRecordData155_valid
  · exact c8FourRecordData156_valid
  · exact c8FourRecordData157_valid
  · exact c8FourRecordData158_valid
  · exact c8FourRecordData159_valid
  · exact c8FourRecordData160_valid
  · exact c8FourRecordData161_valid
  · exact c8FourRecordData162_valid
  · exact c8FourRecordData163_valid
  · exact c8FourRecordData164_valid
  · exact c8FourRecordData165_valid
  · exact c8FourRecordData166_valid
  · exact c8FourRecordData167_valid
  · exact c8FourRecordData168_valid
  · exact c8FourRecordData169_valid
  · exact c8FourRecordData170_valid
  · exact c8FourRecordData171_valid
  · exact c8FourRecordData172_valid
  · exact c8FourRecordData173_valid
  · exact c8FourRecordData174_valid
  · exact c8FourRecordData175_valid
  · exact c8FourRecordData176_valid
  · exact c8FourRecordData177_valid
  · exact c8FourRecordData178_valid
  · exact c8FourRecordData179_valid
  · exact c8FourRecordData180_valid
  · exact c8FourRecordData181_valid
  · exact c8FourRecordData182_valid
  · exact c8FourRecordData183_valid
  · exact c8FourRecordData184_valid
  · exact c8FourRecordData185_valid
  · exact c8FourRecordData186_valid
  · exact c8FourRecordData187_valid
  · exact c8FourRecordData188_valid
  · exact c8FourRecordData189_valid
  · exact c8FourRecordData190_valid
  · exact c8FourRecordData191_valid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk2_kernels (j : Fin 64) :
    c8FourKernelListsValid (c8FourRecordChunk2[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData128_kernels
  · exact c8FourRecordData129_kernels
  · exact c8FourRecordData130_kernels
  · exact c8FourRecordData131_kernels
  · exact c8FourRecordData132_kernels
  · exact c8FourRecordData133_kernels
  · exact c8FourRecordData134_kernels
  · exact c8FourRecordData135_kernels
  · exact c8FourRecordData136_kernels
  · exact c8FourRecordData137_kernels
  · exact c8FourRecordData138_kernels
  · exact c8FourRecordData139_kernels
  · exact c8FourRecordData140_kernels
  · exact c8FourRecordData141_kernels
  · exact c8FourRecordData142_kernels
  · exact c8FourRecordData143_kernels
  · exact c8FourRecordData144_kernels
  · exact c8FourRecordData145_kernels
  · exact c8FourRecordData146_kernels
  · exact c8FourRecordData147_kernels
  · exact c8FourRecordData148_kernels
  · exact c8FourRecordData149_kernels
  · exact c8FourRecordData150_kernels
  · exact c8FourRecordData151_kernels
  · exact c8FourRecordData152_kernels
  · exact c8FourRecordData153_kernels
  · exact c8FourRecordData154_kernels
  · exact c8FourRecordData155_kernels
  · exact c8FourRecordData156_kernels
  · exact c8FourRecordData157_kernels
  · exact c8FourRecordData158_kernels
  · exact c8FourRecordData159_kernels
  · exact c8FourRecordData160_kernels
  · exact c8FourRecordData161_kernels
  · exact c8FourRecordData162_kernels
  · exact c8FourRecordData163_kernels
  · exact c8FourRecordData164_kernels
  · exact c8FourRecordData165_kernels
  · exact c8FourRecordData166_kernels
  · exact c8FourRecordData167_kernels
  · exact c8FourRecordData168_kernels
  · exact c8FourRecordData169_kernels
  · exact c8FourRecordData170_kernels
  · exact c8FourRecordData171_kernels
  · exact c8FourRecordData172_kernels
  · exact c8FourRecordData173_kernels
  · exact c8FourRecordData174_kernels
  · exact c8FourRecordData175_kernels
  · exact c8FourRecordData176_kernels
  · exact c8FourRecordData177_kernels
  · exact c8FourRecordData178_kernels
  · exact c8FourRecordData179_kernels
  · exact c8FourRecordData180_kernels
  · exact c8FourRecordData181_kernels
  · exact c8FourRecordData182_kernels
  · exact c8FourRecordData183_kernels
  · exact c8FourRecordData184_kernels
  · exact c8FourRecordData185_kernels
  · exact c8FourRecordData186_kernels
  · exact c8FourRecordData187_kernels
  · exact c8FourRecordData188_kernels
  · exact c8FourRecordData189_kernels
  · exact c8FourRecordData190_kernels
  · exact c8FourRecordData191_kernels

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk2_vectors (j : Fin 64) :
    c8FourGeneratorVectorsValid (c8FourRecordChunk2[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData128_vectors
  · exact c8FourRecordData129_vectors
  · exact c8FourRecordData130_vectors
  · exact c8FourRecordData131_vectors
  · exact c8FourRecordData132_vectors
  · exact c8FourRecordData133_vectors
  · exact c8FourRecordData134_vectors
  · exact c8FourRecordData135_vectors
  · exact c8FourRecordData136_vectors
  · exact c8FourRecordData137_vectors
  · exact c8FourRecordData138_vectors
  · exact c8FourRecordData139_vectors
  · exact c8FourRecordData140_vectors
  · exact c8FourRecordData141_vectors
  · exact c8FourRecordData142_vectors
  · exact c8FourRecordData143_vectors
  · exact c8FourRecordData144_vectors
  · exact c8FourRecordData145_vectors
  · exact c8FourRecordData146_vectors
  · exact c8FourRecordData147_vectors
  · exact c8FourRecordData148_vectors
  · exact c8FourRecordData149_vectors
  · exact c8FourRecordData150_vectors
  · exact c8FourRecordData151_vectors
  · exact c8FourRecordData152_vectors
  · exact c8FourRecordData153_vectors
  · exact c8FourRecordData154_vectors
  · exact c8FourRecordData155_vectors
  · exact c8FourRecordData156_vectors
  · exact c8FourRecordData157_vectors
  · exact c8FourRecordData158_vectors
  · exact c8FourRecordData159_vectors
  · exact c8FourRecordData160_vectors
  · exact c8FourRecordData161_vectors
  · exact c8FourRecordData162_vectors
  · exact c8FourRecordData163_vectors
  · exact c8FourRecordData164_vectors
  · exact c8FourRecordData165_vectors
  · exact c8FourRecordData166_vectors
  · exact c8FourRecordData167_vectors
  · exact c8FourRecordData168_vectors
  · exact c8FourRecordData169_vectors
  · exact c8FourRecordData170_vectors
  · exact c8FourRecordData171_vectors
  · exact c8FourRecordData172_vectors
  · exact c8FourRecordData173_vectors
  · exact c8FourRecordData174_vectors
  · exact c8FourRecordData175_vectors
  · exact c8FourRecordData176_vectors
  · exact c8FourRecordData177_vectors
  · exact c8FourRecordData178_vectors
  · exact c8FourRecordData179_vectors
  · exact c8FourRecordData180_vectors
  · exact c8FourRecordData181_vectors
  · exact c8FourRecordData182_vectors
  · exact c8FourRecordData183_vectors
  · exact c8FourRecordData184_vectors
  · exact c8FourRecordData185_vectors
  · exact c8FourRecordData186_vectors
  · exact c8FourRecordData187_vectors
  · exact c8FourRecordData188_vectors
  · exact c8FourRecordData189_vectors
  · exact c8FourRecordData190_vectors
  · exact c8FourRecordData191_vectors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk2_rank_cards (j : Fin 64) :
    (c8FourRecordBinaryImages (c8FourRecordChunk2[j.val]!)).card = 2 ^ (c8FourRecordChunk2[j.val]!).generators.length := by
  fin_cases j
  · change (c8FourRecordBinaryImages c8FourRecordData128).card = 2 ^ c8FourRecordData128.generators.length
    rw [(c8FourRecordData128_rank_card).2]
    exact (c8FourRecordData128_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData129).card = 2 ^ c8FourRecordData129.generators.length
    rw [(c8FourRecordData129_rank_card).2]
    exact (c8FourRecordData129_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData130).card = 2 ^ c8FourRecordData130.generators.length
    rw [(c8FourRecordData130_rank_card).2]
    exact (c8FourRecordData130_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData131).card = 2 ^ c8FourRecordData131.generators.length
    rw [(c8FourRecordData131_rank_card).2]
    exact (c8FourRecordData131_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData132).card = 2 ^ c8FourRecordData132.generators.length
    rw [(c8FourRecordData132_rank_card).2]
    exact (c8FourRecordData132_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData133).card = 2 ^ c8FourRecordData133.generators.length
    rw [(c8FourRecordData133_rank_card).2]
    exact (c8FourRecordData133_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData134).card = 2 ^ c8FourRecordData134.generators.length
    rw [(c8FourRecordData134_rank_card).2]
    exact (c8FourRecordData134_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData135).card = 2 ^ c8FourRecordData135.generators.length
    rw [(c8FourRecordData135_rank_card).2]
    exact (c8FourRecordData135_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData136).card = 2 ^ c8FourRecordData136.generators.length
    rw [(c8FourRecordData136_rank_card).2]
    exact (c8FourRecordData136_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData137).card = 2 ^ c8FourRecordData137.generators.length
    rw [(c8FourRecordData137_rank_card).2]
    exact (c8FourRecordData137_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData138).card = 2 ^ c8FourRecordData138.generators.length
    rw [(c8FourRecordData138_rank_card).2]
    exact (c8FourRecordData138_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData139).card = 2 ^ c8FourRecordData139.generators.length
    rw [(c8FourRecordData139_rank_card).2]
    exact (c8FourRecordData139_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData140).card = 2 ^ c8FourRecordData140.generators.length
    rw [(c8FourRecordData140_rank_card).2]
    exact (c8FourRecordData140_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData141).card = 2 ^ c8FourRecordData141.generators.length
    rw [(c8FourRecordData141_rank_card).2]
    exact (c8FourRecordData141_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData142).card = 2 ^ c8FourRecordData142.generators.length
    rw [(c8FourRecordData142_rank_card).2]
    exact (c8FourRecordData142_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData143).card = 2 ^ c8FourRecordData143.generators.length
    rw [(c8FourRecordData143_rank_card).2]
    exact (c8FourRecordData143_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData144).card = 2 ^ c8FourRecordData144.generators.length
    rw [(c8FourRecordData144_rank_card).2]
    exact (c8FourRecordData144_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData145).card = 2 ^ c8FourRecordData145.generators.length
    rw [(c8FourRecordData145_rank_card).2]
    exact (c8FourRecordData145_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData146).card = 2 ^ c8FourRecordData146.generators.length
    rw [(c8FourRecordData146_rank_card).2]
    exact (c8FourRecordData146_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData147).card = 2 ^ c8FourRecordData147.generators.length
    rw [(c8FourRecordData147_rank_card).2]
    exact (c8FourRecordData147_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData148).card = 2 ^ c8FourRecordData148.generators.length
    rw [(c8FourRecordData148_rank_card).2]
    exact (c8FourRecordData148_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData149).card = 2 ^ c8FourRecordData149.generators.length
    rw [(c8FourRecordData149_rank_card).2]
    exact (c8FourRecordData149_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData150).card = 2 ^ c8FourRecordData150.generators.length
    rw [(c8FourRecordData150_rank_card).2]
    exact (c8FourRecordData150_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData151).card = 2 ^ c8FourRecordData151.generators.length
    rw [(c8FourRecordData151_rank_card).2]
    exact (c8FourRecordData151_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData152).card = 2 ^ c8FourRecordData152.generators.length
    rw [(c8FourRecordData152_rank_card).2]
    exact (c8FourRecordData152_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData153).card = 2 ^ c8FourRecordData153.generators.length
    rw [(c8FourRecordData153_rank_card).2]
    exact (c8FourRecordData153_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData154).card = 2 ^ c8FourRecordData154.generators.length
    rw [(c8FourRecordData154_rank_card).2]
    exact (c8FourRecordData154_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData155).card = 2 ^ c8FourRecordData155.generators.length
    rw [(c8FourRecordData155_rank_card).2]
    exact (c8FourRecordData155_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData156).card = 2 ^ c8FourRecordData156.generators.length
    rw [(c8FourRecordData156_rank_card).2]
    exact (c8FourRecordData156_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData157).card = 2 ^ c8FourRecordData157.generators.length
    rw [(c8FourRecordData157_rank_card).2]
    exact (c8FourRecordData157_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData158).card = 2 ^ c8FourRecordData158.generators.length
    rw [(c8FourRecordData158_rank_card).2]
    exact (c8FourRecordData158_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData159).card = 2 ^ c8FourRecordData159.generators.length
    rw [(c8FourRecordData159_rank_card).2]
    exact (c8FourRecordData159_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData160).card = 2 ^ c8FourRecordData160.generators.length
    rw [(c8FourRecordData160_rank_card).2]
    exact (c8FourRecordData160_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData161).card = 2 ^ c8FourRecordData161.generators.length
    rw [(c8FourRecordData161_rank_card).2]
    exact (c8FourRecordData161_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData162).card = 2 ^ c8FourRecordData162.generators.length
    rw [(c8FourRecordData162_rank_card).2]
    exact (c8FourRecordData162_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData163).card = 2 ^ c8FourRecordData163.generators.length
    rw [(c8FourRecordData163_rank_card).2]
    exact (c8FourRecordData163_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData164).card = 2 ^ c8FourRecordData164.generators.length
    rw [(c8FourRecordData164_rank_card).2]
    exact (c8FourRecordData164_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData165).card = 2 ^ c8FourRecordData165.generators.length
    rw [(c8FourRecordData165_rank_card).2]
    exact (c8FourRecordData165_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData166).card = 2 ^ c8FourRecordData166.generators.length
    rw [(c8FourRecordData166_rank_card).2]
    exact (c8FourRecordData166_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData167).card = 2 ^ c8FourRecordData167.generators.length
    rw [(c8FourRecordData167_rank_card).2]
    exact (c8FourRecordData167_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData168).card = 2 ^ c8FourRecordData168.generators.length
    rw [(c8FourRecordData168_rank_card).2]
    exact (c8FourRecordData168_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData169).card = 2 ^ c8FourRecordData169.generators.length
    rw [(c8FourRecordData169_rank_card).2]
    exact (c8FourRecordData169_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData170).card = 2 ^ c8FourRecordData170.generators.length
    rw [(c8FourRecordData170_rank_card).2]
    exact (c8FourRecordData170_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData171).card = 2 ^ c8FourRecordData171.generators.length
    rw [(c8FourRecordData171_rank_card).2]
    exact (c8FourRecordData171_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData172).card = 2 ^ c8FourRecordData172.generators.length
    rw [(c8FourRecordData172_rank_card).2]
    exact (c8FourRecordData172_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData173).card = 2 ^ c8FourRecordData173.generators.length
    rw [(c8FourRecordData173_rank_card).2]
    exact (c8FourRecordData173_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData174).card = 2 ^ c8FourRecordData174.generators.length
    rw [(c8FourRecordData174_rank_card).2]
    exact (c8FourRecordData174_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData175).card = 2 ^ c8FourRecordData175.generators.length
    rw [(c8FourRecordData175_rank_card).2]
    exact (c8FourRecordData175_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData176).card = 2 ^ c8FourRecordData176.generators.length
    rw [(c8FourRecordData176_rank_card).2]
    exact (c8FourRecordData176_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData177).card = 2 ^ c8FourRecordData177.generators.length
    rw [(c8FourRecordData177_rank_card).2]
    exact (c8FourRecordData177_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData178).card = 2 ^ c8FourRecordData178.generators.length
    rw [(c8FourRecordData178_rank_card).2]
    exact (c8FourRecordData178_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData179).card = 2 ^ c8FourRecordData179.generators.length
    rw [(c8FourRecordData179_rank_card).2]
    exact (c8FourRecordData179_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData180).card = 2 ^ c8FourRecordData180.generators.length
    rw [(c8FourRecordData180_rank_card).2]
    exact (c8FourRecordData180_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData181).card = 2 ^ c8FourRecordData181.generators.length
    rw [(c8FourRecordData181_rank_card).2]
    exact (c8FourRecordData181_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData182).card = 2 ^ c8FourRecordData182.generators.length
    rw [(c8FourRecordData182_rank_card).2]
    exact (c8FourRecordData182_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData183).card = 2 ^ c8FourRecordData183.generators.length
    rw [(c8FourRecordData183_rank_card).2]
    exact (c8FourRecordData183_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData184).card = 2 ^ c8FourRecordData184.generators.length
    rw [(c8FourRecordData184_rank_card).2]
    exact (c8FourRecordData184_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData185).card = 2 ^ c8FourRecordData185.generators.length
    rw [(c8FourRecordData185_rank_card).2]
    exact (c8FourRecordData185_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData186).card = 2 ^ c8FourRecordData186.generators.length
    rw [(c8FourRecordData186_rank_card).2]
    exact (c8FourRecordData186_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData187).card = 2 ^ c8FourRecordData187.generators.length
    rw [(c8FourRecordData187_rank_card).2]
    exact (c8FourRecordData187_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData188).card = 2 ^ c8FourRecordData188.generators.length
    rw [(c8FourRecordData188_rank_card).2]
    exact (c8FourRecordData188_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData189).card = 2 ^ c8FourRecordData189.generators.length
    rw [(c8FourRecordData189_rank_card).2]
    exact (c8FourRecordData189_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData190).card = 2 ^ c8FourRecordData190.generators.length
    rw [(c8FourRecordData190_rank_card).2]
    exact (c8FourRecordData190_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData191).card = 2 ^ c8FourRecordData191.generators.length
    rw [(c8FourRecordData191_rank_card).2]
    exact (c8FourRecordData191_rank_card).1

end CFSG.LargeEvenClassification.Helpers
