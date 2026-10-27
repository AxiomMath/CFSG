module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupValid3
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupKernel3
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRank3

public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk3_valid (j : Fin 64) :
    c8FourRecordValid (c8FourRecordChunk3[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData192_valid
  · exact c8FourRecordData193_valid
  · exact c8FourRecordData194_valid
  · exact c8FourRecordData195_valid
  · exact c8FourRecordData196_valid
  · exact c8FourRecordData197_valid
  · exact c8FourRecordData198_valid
  · exact c8FourRecordData199_valid
  · exact c8FourRecordData200_valid
  · exact c8FourRecordData201_valid
  · exact c8FourRecordData202_valid
  · exact c8FourRecordData203_valid
  · exact c8FourRecordData204_valid
  · exact c8FourRecordData205_valid
  · exact c8FourRecordData206_valid
  · exact c8FourRecordData207_valid
  · exact c8FourRecordData208_valid
  · exact c8FourRecordData209_valid
  · exact c8FourRecordData210_valid
  · exact c8FourRecordData211_valid
  · exact c8FourRecordData212_valid
  · exact c8FourRecordData213_valid
  · exact c8FourRecordData214_valid
  · exact c8FourRecordData215_valid
  · exact c8FourRecordData216_valid
  · exact c8FourRecordData217_valid
  · exact c8FourRecordData218_valid
  · exact c8FourRecordData219_valid
  · exact c8FourRecordData220_valid
  · exact c8FourRecordData221_valid
  · exact c8FourRecordData222_valid
  · exact c8FourRecordData223_valid
  · exact c8FourRecordData224_valid
  · exact c8FourRecordData225_valid
  · exact c8FourRecordData226_valid
  · exact c8FourRecordData227_valid
  · exact c8FourRecordData228_valid
  · exact c8FourRecordData229_valid
  · exact c8FourRecordData230_valid
  · exact c8FourRecordData231_valid
  · exact c8FourRecordData232_valid
  · exact c8FourRecordData233_valid
  · exact c8FourRecordData234_valid
  · exact c8FourRecordData235_valid
  · exact c8FourRecordData236_valid
  · exact c8FourRecordData237_valid
  · exact c8FourRecordData238_valid
  · exact c8FourRecordData239_valid
  · exact c8FourRecordData240_valid
  · exact c8FourRecordData241_valid
  · exact c8FourRecordData242_valid
  · exact c8FourRecordData243_valid
  · exact c8FourRecordData244_valid
  · exact c8FourRecordData245_valid
  · exact c8FourRecordData246_valid
  · exact c8FourRecordData247_valid
  · exact c8FourRecordData248_valid
  · exact c8FourRecordData249_valid
  · exact c8FourRecordData250_valid
  · exact c8FourRecordData251_valid
  · exact c8FourRecordData252_valid
  · exact c8FourRecordData253_valid
  · exact c8FourRecordData254_valid
  · exact c8FourRecordData255_valid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk3_kernels (j : Fin 64) :
    c8FourKernelListsValid (c8FourRecordChunk3[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData192_kernels
  · exact c8FourRecordData193_kernels
  · exact c8FourRecordData194_kernels
  · exact c8FourRecordData195_kernels
  · exact c8FourRecordData196_kernels
  · exact c8FourRecordData197_kernels
  · exact c8FourRecordData198_kernels
  · exact c8FourRecordData199_kernels
  · exact c8FourRecordData200_kernels
  · exact c8FourRecordData201_kernels
  · exact c8FourRecordData202_kernels
  · exact c8FourRecordData203_kernels
  · exact c8FourRecordData204_kernels
  · exact c8FourRecordData205_kernels
  · exact c8FourRecordData206_kernels
  · exact c8FourRecordData207_kernels
  · exact c8FourRecordData208_kernels
  · exact c8FourRecordData209_kernels
  · exact c8FourRecordData210_kernels
  · exact c8FourRecordData211_kernels
  · exact c8FourRecordData212_kernels
  · exact c8FourRecordData213_kernels
  · exact c8FourRecordData214_kernels
  · exact c8FourRecordData215_kernels
  · exact c8FourRecordData216_kernels
  · exact c8FourRecordData217_kernels
  · exact c8FourRecordData218_kernels
  · exact c8FourRecordData219_kernels
  · exact c8FourRecordData220_kernels
  · exact c8FourRecordData221_kernels
  · exact c8FourRecordData222_kernels
  · exact c8FourRecordData223_kernels
  · exact c8FourRecordData224_kernels
  · exact c8FourRecordData225_kernels
  · exact c8FourRecordData226_kernels
  · exact c8FourRecordData227_kernels
  · exact c8FourRecordData228_kernels
  · exact c8FourRecordData229_kernels
  · exact c8FourRecordData230_kernels
  · exact c8FourRecordData231_kernels
  · exact c8FourRecordData232_kernels
  · exact c8FourRecordData233_kernels
  · exact c8FourRecordData234_kernels
  · exact c8FourRecordData235_kernels
  · exact c8FourRecordData236_kernels
  · exact c8FourRecordData237_kernels
  · exact c8FourRecordData238_kernels
  · exact c8FourRecordData239_kernels
  · exact c8FourRecordData240_kernels
  · exact c8FourRecordData241_kernels
  · exact c8FourRecordData242_kernels
  · exact c8FourRecordData243_kernels
  · exact c8FourRecordData244_kernels
  · exact c8FourRecordData245_kernels
  · exact c8FourRecordData246_kernels
  · exact c8FourRecordData247_kernels
  · exact c8FourRecordData248_kernels
  · exact c8FourRecordData249_kernels
  · exact c8FourRecordData250_kernels
  · exact c8FourRecordData251_kernels
  · exact c8FourRecordData252_kernels
  · exact c8FourRecordData253_kernels
  · exact c8FourRecordData254_kernels
  · exact c8FourRecordData255_kernels

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk3_vectors (j : Fin 64) :
    c8FourGeneratorVectorsValid (c8FourRecordChunk3[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData192_vectors
  · exact c8FourRecordData193_vectors
  · exact c8FourRecordData194_vectors
  · exact c8FourRecordData195_vectors
  · exact c8FourRecordData196_vectors
  · exact c8FourRecordData197_vectors
  · exact c8FourRecordData198_vectors
  · exact c8FourRecordData199_vectors
  · exact c8FourRecordData200_vectors
  · exact c8FourRecordData201_vectors
  · exact c8FourRecordData202_vectors
  · exact c8FourRecordData203_vectors
  · exact c8FourRecordData204_vectors
  · exact c8FourRecordData205_vectors
  · exact c8FourRecordData206_vectors
  · exact c8FourRecordData207_vectors
  · exact c8FourRecordData208_vectors
  · exact c8FourRecordData209_vectors
  · exact c8FourRecordData210_vectors
  · exact c8FourRecordData211_vectors
  · exact c8FourRecordData212_vectors
  · exact c8FourRecordData213_vectors
  · exact c8FourRecordData214_vectors
  · exact c8FourRecordData215_vectors
  · exact c8FourRecordData216_vectors
  · exact c8FourRecordData217_vectors
  · exact c8FourRecordData218_vectors
  · exact c8FourRecordData219_vectors
  · exact c8FourRecordData220_vectors
  · exact c8FourRecordData221_vectors
  · exact c8FourRecordData222_vectors
  · exact c8FourRecordData223_vectors
  · exact c8FourRecordData224_vectors
  · exact c8FourRecordData225_vectors
  · exact c8FourRecordData226_vectors
  · exact c8FourRecordData227_vectors
  · exact c8FourRecordData228_vectors
  · exact c8FourRecordData229_vectors
  · exact c8FourRecordData230_vectors
  · exact c8FourRecordData231_vectors
  · exact c8FourRecordData232_vectors
  · exact c8FourRecordData233_vectors
  · exact c8FourRecordData234_vectors
  · exact c8FourRecordData235_vectors
  · exact c8FourRecordData236_vectors
  · exact c8FourRecordData237_vectors
  · exact c8FourRecordData238_vectors
  · exact c8FourRecordData239_vectors
  · exact c8FourRecordData240_vectors
  · exact c8FourRecordData241_vectors
  · exact c8FourRecordData242_vectors
  · exact c8FourRecordData243_vectors
  · exact c8FourRecordData244_vectors
  · exact c8FourRecordData245_vectors
  · exact c8FourRecordData246_vectors
  · exact c8FourRecordData247_vectors
  · exact c8FourRecordData248_vectors
  · exact c8FourRecordData249_vectors
  · exact c8FourRecordData250_vectors
  · exact c8FourRecordData251_vectors
  · exact c8FourRecordData252_vectors
  · exact c8FourRecordData253_vectors
  · exact c8FourRecordData254_vectors
  · exact c8FourRecordData255_vectors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk3_rank_cards (j : Fin 64) :
    (c8FourRecordBinaryImages (c8FourRecordChunk3[j.val]!)).card = 2 ^ (c8FourRecordChunk3[j.val]!).generators.length := by
  fin_cases j
  · change (c8FourRecordBinaryImages c8FourRecordData192).card = 2 ^ c8FourRecordData192.generators.length
    rw [(c8FourRecordData192_rank_card).2]
    exact (c8FourRecordData192_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData193).card = 2 ^ c8FourRecordData193.generators.length
    rw [(c8FourRecordData193_rank_card).2]
    exact (c8FourRecordData193_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData194).card = 2 ^ c8FourRecordData194.generators.length
    rw [(c8FourRecordData194_rank_card).2]
    exact (c8FourRecordData194_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData195).card = 2 ^ c8FourRecordData195.generators.length
    rw [(c8FourRecordData195_rank_card).2]
    exact (c8FourRecordData195_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData196).card = 2 ^ c8FourRecordData196.generators.length
    rw [(c8FourRecordData196_rank_card).2]
    exact (c8FourRecordData196_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData197).card = 2 ^ c8FourRecordData197.generators.length
    rw [(c8FourRecordData197_rank_card).2]
    exact (c8FourRecordData197_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData198).card = 2 ^ c8FourRecordData198.generators.length
    rw [(c8FourRecordData198_rank_card).2]
    exact (c8FourRecordData198_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData199).card = 2 ^ c8FourRecordData199.generators.length
    rw [(c8FourRecordData199_rank_card).2]
    exact (c8FourRecordData199_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData200).card = 2 ^ c8FourRecordData200.generators.length
    rw [(c8FourRecordData200_rank_card).2]
    exact (c8FourRecordData200_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData201).card = 2 ^ c8FourRecordData201.generators.length
    rw [(c8FourRecordData201_rank_card).2]
    exact (c8FourRecordData201_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData202).card = 2 ^ c8FourRecordData202.generators.length
    rw [(c8FourRecordData202_rank_card).2]
    exact (c8FourRecordData202_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData203).card = 2 ^ c8FourRecordData203.generators.length
    rw [(c8FourRecordData203_rank_card).2]
    exact (c8FourRecordData203_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData204).card = 2 ^ c8FourRecordData204.generators.length
    rw [(c8FourRecordData204_rank_card).2]
    exact (c8FourRecordData204_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData205).card = 2 ^ c8FourRecordData205.generators.length
    rw [(c8FourRecordData205_rank_card).2]
    exact (c8FourRecordData205_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData206).card = 2 ^ c8FourRecordData206.generators.length
    rw [(c8FourRecordData206_rank_card).2]
    exact (c8FourRecordData206_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData207).card = 2 ^ c8FourRecordData207.generators.length
    rw [(c8FourRecordData207_rank_card).2]
    exact (c8FourRecordData207_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData208).card = 2 ^ c8FourRecordData208.generators.length
    rw [(c8FourRecordData208_rank_card).2]
    exact (c8FourRecordData208_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData209).card = 2 ^ c8FourRecordData209.generators.length
    rw [(c8FourRecordData209_rank_card).2]
    exact (c8FourRecordData209_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData210).card = 2 ^ c8FourRecordData210.generators.length
    rw [(c8FourRecordData210_rank_card).2]
    exact (c8FourRecordData210_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData211).card = 2 ^ c8FourRecordData211.generators.length
    rw [(c8FourRecordData211_rank_card).2]
    exact (c8FourRecordData211_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData212).card = 2 ^ c8FourRecordData212.generators.length
    rw [(c8FourRecordData212_rank_card).2]
    exact (c8FourRecordData212_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData213).card = 2 ^ c8FourRecordData213.generators.length
    rw [(c8FourRecordData213_rank_card).2]
    exact (c8FourRecordData213_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData214).card = 2 ^ c8FourRecordData214.generators.length
    rw [(c8FourRecordData214_rank_card).2]
    exact (c8FourRecordData214_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData215).card = 2 ^ c8FourRecordData215.generators.length
    rw [(c8FourRecordData215_rank_card).2]
    exact (c8FourRecordData215_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData216).card = 2 ^ c8FourRecordData216.generators.length
    rw [(c8FourRecordData216_rank_card).2]
    exact (c8FourRecordData216_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData217).card = 2 ^ c8FourRecordData217.generators.length
    rw [(c8FourRecordData217_rank_card).2]
    exact (c8FourRecordData217_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData218).card = 2 ^ c8FourRecordData218.generators.length
    rw [(c8FourRecordData218_rank_card).2]
    exact (c8FourRecordData218_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData219).card = 2 ^ c8FourRecordData219.generators.length
    rw [(c8FourRecordData219_rank_card).2]
    exact (c8FourRecordData219_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData220).card = 2 ^ c8FourRecordData220.generators.length
    rw [(c8FourRecordData220_rank_card).2]
    exact (c8FourRecordData220_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData221).card = 2 ^ c8FourRecordData221.generators.length
    rw [(c8FourRecordData221_rank_card).2]
    exact (c8FourRecordData221_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData222).card = 2 ^ c8FourRecordData222.generators.length
    rw [(c8FourRecordData222_rank_card).2]
    exact (c8FourRecordData222_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData223).card = 2 ^ c8FourRecordData223.generators.length
    rw [(c8FourRecordData223_rank_card).2]
    exact (c8FourRecordData223_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData224).card = 2 ^ c8FourRecordData224.generators.length
    rw [(c8FourRecordData224_rank_card).2]
    exact (c8FourRecordData224_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData225).card = 2 ^ c8FourRecordData225.generators.length
    rw [(c8FourRecordData225_rank_card).2]
    exact (c8FourRecordData225_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData226).card = 2 ^ c8FourRecordData226.generators.length
    rw [(c8FourRecordData226_rank_card).2]
    exact (c8FourRecordData226_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData227).card = 2 ^ c8FourRecordData227.generators.length
    rw [(c8FourRecordData227_rank_card).2]
    exact (c8FourRecordData227_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData228).card = 2 ^ c8FourRecordData228.generators.length
    rw [(c8FourRecordData228_rank_card).2]
    exact (c8FourRecordData228_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData229).card = 2 ^ c8FourRecordData229.generators.length
    rw [(c8FourRecordData229_rank_card).2]
    exact (c8FourRecordData229_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData230).card = 2 ^ c8FourRecordData230.generators.length
    rw [(c8FourRecordData230_rank_card).2]
    exact (c8FourRecordData230_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData231).card = 2 ^ c8FourRecordData231.generators.length
    rw [(c8FourRecordData231_rank_card).2]
    exact (c8FourRecordData231_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData232).card = 2 ^ c8FourRecordData232.generators.length
    rw [(c8FourRecordData232_rank_card).2]
    exact (c8FourRecordData232_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData233).card = 2 ^ c8FourRecordData233.generators.length
    rw [(c8FourRecordData233_rank_card).2]
    exact (c8FourRecordData233_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData234).card = 2 ^ c8FourRecordData234.generators.length
    rw [(c8FourRecordData234_rank_card).2]
    exact (c8FourRecordData234_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData235).card = 2 ^ c8FourRecordData235.generators.length
    rw [(c8FourRecordData235_rank_card).2]
    exact (c8FourRecordData235_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData236).card = 2 ^ c8FourRecordData236.generators.length
    rw [(c8FourRecordData236_rank_card).2]
    exact (c8FourRecordData236_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData237).card = 2 ^ c8FourRecordData237.generators.length
    rw [(c8FourRecordData237_rank_card).2]
    exact (c8FourRecordData237_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData238).card = 2 ^ c8FourRecordData238.generators.length
    rw [(c8FourRecordData238_rank_card).2]
    exact (c8FourRecordData238_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData239).card = 2 ^ c8FourRecordData239.generators.length
    rw [(c8FourRecordData239_rank_card).2]
    exact (c8FourRecordData239_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData240).card = 2 ^ c8FourRecordData240.generators.length
    rw [(c8FourRecordData240_rank_card).2]
    exact (c8FourRecordData240_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData241).card = 2 ^ c8FourRecordData241.generators.length
    rw [(c8FourRecordData241_rank_card).2]
    exact (c8FourRecordData241_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData242).card = 2 ^ c8FourRecordData242.generators.length
    rw [(c8FourRecordData242_rank_card).2]
    exact (c8FourRecordData242_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData243).card = 2 ^ c8FourRecordData243.generators.length
    rw [(c8FourRecordData243_rank_card).2]
    exact (c8FourRecordData243_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData244).card = 2 ^ c8FourRecordData244.generators.length
    rw [(c8FourRecordData244_rank_card).2]
    exact (c8FourRecordData244_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData245).card = 2 ^ c8FourRecordData245.generators.length
    rw [(c8FourRecordData245_rank_card).2]
    exact (c8FourRecordData245_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData246).card = 2 ^ c8FourRecordData246.generators.length
    rw [(c8FourRecordData246_rank_card).2]
    exact (c8FourRecordData246_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData247).card = 2 ^ c8FourRecordData247.generators.length
    rw [(c8FourRecordData247_rank_card).2]
    exact (c8FourRecordData247_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData248).card = 2 ^ c8FourRecordData248.generators.length
    rw [(c8FourRecordData248_rank_card).2]
    exact (c8FourRecordData248_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData249).card = 2 ^ c8FourRecordData249.generators.length
    rw [(c8FourRecordData249_rank_card).2]
    exact (c8FourRecordData249_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData250).card = 2 ^ c8FourRecordData250.generators.length
    rw [(c8FourRecordData250_rank_card).2]
    exact (c8FourRecordData250_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData251).card = 2 ^ c8FourRecordData251.generators.length
    rw [(c8FourRecordData251_rank_card).2]
    exact (c8FourRecordData251_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData252).card = 2 ^ c8FourRecordData252.generators.length
    rw [(c8FourRecordData252_rank_card).2]
    exact (c8FourRecordData252_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData253).card = 2 ^ c8FourRecordData253.generators.length
    rw [(c8FourRecordData253_rank_card).2]
    exact (c8FourRecordData253_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData254).card = 2 ^ c8FourRecordData254.generators.length
    rw [(c8FourRecordData254_rank_card).2]
    exact (c8FourRecordData254_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData255).card = 2 ^ c8FourRecordData255.generators.length
    rw [(c8FourRecordData255_rank_card).2]
    exact (c8FourRecordData255_rank_card).1

end CFSG.LargeEvenClassification.Helpers
