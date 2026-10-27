module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupValid12
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupKernel12
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRank12

public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk12_valid (j : Fin 64) :
    c8FourRecordValid (c8FourRecordChunk12[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData768_valid
  · exact c8FourRecordData769_valid
  · exact c8FourRecordData770_valid
  · exact c8FourRecordData771_valid
  · exact c8FourRecordData772_valid
  · exact c8FourRecordData773_valid
  · exact c8FourRecordData774_valid
  · exact c8FourRecordData775_valid
  · exact c8FourRecordData776_valid
  · exact c8FourRecordData777_valid
  · exact c8FourRecordData778_valid
  · exact c8FourRecordData779_valid
  · exact c8FourRecordData780_valid
  · exact c8FourRecordData781_valid
  · exact c8FourRecordData782_valid
  · exact c8FourRecordData783_valid
  · exact c8FourRecordData784_valid
  · exact c8FourRecordData785_valid
  · exact c8FourRecordData786_valid
  · exact c8FourRecordData787_valid
  · exact c8FourRecordData788_valid
  · exact c8FourRecordData789_valid
  · exact c8FourRecordData790_valid
  · exact c8FourRecordData791_valid
  · exact c8FourRecordData792_valid
  · exact c8FourRecordData793_valid
  · exact c8FourRecordData794_valid
  · exact c8FourRecordData795_valid
  · exact c8FourRecordData796_valid
  · exact c8FourRecordData797_valid
  · exact c8FourRecordData798_valid
  · exact c8FourRecordData799_valid
  · exact c8FourRecordData800_valid
  · exact c8FourRecordData801_valid
  · exact c8FourRecordData802_valid
  · exact c8FourRecordData803_valid
  · exact c8FourRecordData804_valid
  · exact c8FourRecordData805_valid
  · exact c8FourRecordData806_valid
  · exact c8FourRecordData807_valid
  · exact c8FourRecordData808_valid
  · exact c8FourRecordData809_valid
  · exact c8FourRecordData810_valid
  · exact c8FourRecordData811_valid
  · exact c8FourRecordData812_valid
  · exact c8FourRecordData813_valid
  · exact c8FourRecordData814_valid
  · exact c8FourRecordData815_valid
  · exact c8FourRecordData816_valid
  · exact c8FourRecordData817_valid
  · exact c8FourRecordData818_valid
  · exact c8FourRecordData819_valid
  · exact c8FourRecordData820_valid
  · exact c8FourRecordData821_valid
  · exact c8FourRecordData822_valid
  · exact c8FourRecordData823_valid
  · exact c8FourRecordData824_valid
  · exact c8FourRecordData825_valid
  · exact c8FourRecordData826_valid
  · exact c8FourRecordData827_valid
  · exact c8FourRecordData828_valid
  · exact c8FourRecordData829_valid
  · exact c8FourRecordData830_valid
  · exact c8FourRecordData831_valid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk12_kernels (j : Fin 64) :
    c8FourKernelListsValid (c8FourRecordChunk12[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData768_kernels
  · exact c8FourRecordData769_kernels
  · exact c8FourRecordData770_kernels
  · exact c8FourRecordData771_kernels
  · exact c8FourRecordData772_kernels
  · exact c8FourRecordData773_kernels
  · exact c8FourRecordData774_kernels
  · exact c8FourRecordData775_kernels
  · exact c8FourRecordData776_kernels
  · exact c8FourRecordData777_kernels
  · exact c8FourRecordData778_kernels
  · exact c8FourRecordData779_kernels
  · exact c8FourRecordData780_kernels
  · exact c8FourRecordData781_kernels
  · exact c8FourRecordData782_kernels
  · exact c8FourRecordData783_kernels
  · exact c8FourRecordData784_kernels
  · exact c8FourRecordData785_kernels
  · exact c8FourRecordData786_kernels
  · exact c8FourRecordData787_kernels
  · exact c8FourRecordData788_kernels
  · exact c8FourRecordData789_kernels
  · exact c8FourRecordData790_kernels
  · exact c8FourRecordData791_kernels
  · exact c8FourRecordData792_kernels
  · exact c8FourRecordData793_kernels
  · exact c8FourRecordData794_kernels
  · exact c8FourRecordData795_kernels
  · exact c8FourRecordData796_kernels
  · exact c8FourRecordData797_kernels
  · exact c8FourRecordData798_kernels
  · exact c8FourRecordData799_kernels
  · exact c8FourRecordData800_kernels
  · exact c8FourRecordData801_kernels
  · exact c8FourRecordData802_kernels
  · exact c8FourRecordData803_kernels
  · exact c8FourRecordData804_kernels
  · exact c8FourRecordData805_kernels
  · exact c8FourRecordData806_kernels
  · exact c8FourRecordData807_kernels
  · exact c8FourRecordData808_kernels
  · exact c8FourRecordData809_kernels
  · exact c8FourRecordData810_kernels
  · exact c8FourRecordData811_kernels
  · exact c8FourRecordData812_kernels
  · exact c8FourRecordData813_kernels
  · exact c8FourRecordData814_kernels
  · exact c8FourRecordData815_kernels
  · exact c8FourRecordData816_kernels
  · exact c8FourRecordData817_kernels
  · exact c8FourRecordData818_kernels
  · exact c8FourRecordData819_kernels
  · exact c8FourRecordData820_kernels
  · exact c8FourRecordData821_kernels
  · exact c8FourRecordData822_kernels
  · exact c8FourRecordData823_kernels
  · exact c8FourRecordData824_kernels
  · exact c8FourRecordData825_kernels
  · exact c8FourRecordData826_kernels
  · exact c8FourRecordData827_kernels
  · exact c8FourRecordData828_kernels
  · exact c8FourRecordData829_kernels
  · exact c8FourRecordData830_kernels
  · exact c8FourRecordData831_kernels

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk12_vectors (j : Fin 64) :
    c8FourGeneratorVectorsValid (c8FourRecordChunk12[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData768_vectors
  · exact c8FourRecordData769_vectors
  · exact c8FourRecordData770_vectors
  · exact c8FourRecordData771_vectors
  · exact c8FourRecordData772_vectors
  · exact c8FourRecordData773_vectors
  · exact c8FourRecordData774_vectors
  · exact c8FourRecordData775_vectors
  · exact c8FourRecordData776_vectors
  · exact c8FourRecordData777_vectors
  · exact c8FourRecordData778_vectors
  · exact c8FourRecordData779_vectors
  · exact c8FourRecordData780_vectors
  · exact c8FourRecordData781_vectors
  · exact c8FourRecordData782_vectors
  · exact c8FourRecordData783_vectors
  · exact c8FourRecordData784_vectors
  · exact c8FourRecordData785_vectors
  · exact c8FourRecordData786_vectors
  · exact c8FourRecordData787_vectors
  · exact c8FourRecordData788_vectors
  · exact c8FourRecordData789_vectors
  · exact c8FourRecordData790_vectors
  · exact c8FourRecordData791_vectors
  · exact c8FourRecordData792_vectors
  · exact c8FourRecordData793_vectors
  · exact c8FourRecordData794_vectors
  · exact c8FourRecordData795_vectors
  · exact c8FourRecordData796_vectors
  · exact c8FourRecordData797_vectors
  · exact c8FourRecordData798_vectors
  · exact c8FourRecordData799_vectors
  · exact c8FourRecordData800_vectors
  · exact c8FourRecordData801_vectors
  · exact c8FourRecordData802_vectors
  · exact c8FourRecordData803_vectors
  · exact c8FourRecordData804_vectors
  · exact c8FourRecordData805_vectors
  · exact c8FourRecordData806_vectors
  · exact c8FourRecordData807_vectors
  · exact c8FourRecordData808_vectors
  · exact c8FourRecordData809_vectors
  · exact c8FourRecordData810_vectors
  · exact c8FourRecordData811_vectors
  · exact c8FourRecordData812_vectors
  · exact c8FourRecordData813_vectors
  · exact c8FourRecordData814_vectors
  · exact c8FourRecordData815_vectors
  · exact c8FourRecordData816_vectors
  · exact c8FourRecordData817_vectors
  · exact c8FourRecordData818_vectors
  · exact c8FourRecordData819_vectors
  · exact c8FourRecordData820_vectors
  · exact c8FourRecordData821_vectors
  · exact c8FourRecordData822_vectors
  · exact c8FourRecordData823_vectors
  · exact c8FourRecordData824_vectors
  · exact c8FourRecordData825_vectors
  · exact c8FourRecordData826_vectors
  · exact c8FourRecordData827_vectors
  · exact c8FourRecordData828_vectors
  · exact c8FourRecordData829_vectors
  · exact c8FourRecordData830_vectors
  · exact c8FourRecordData831_vectors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk12_rank_cards (j : Fin 64) :
    (c8FourRecordBinaryImages (c8FourRecordChunk12[j.val]!)).card = 2 ^ (c8FourRecordChunk12[j.val]!).generators.length := by
  fin_cases j
  · change (c8FourRecordBinaryImages c8FourRecordData768).card = 2 ^ c8FourRecordData768.generators.length
    rw [(c8FourRecordData768_rank_card).2]
    exact (c8FourRecordData768_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData769).card = 2 ^ c8FourRecordData769.generators.length
    rw [(c8FourRecordData769_rank_card).2]
    exact (c8FourRecordData769_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData770).card = 2 ^ c8FourRecordData770.generators.length
    rw [(c8FourRecordData770_rank_card).2]
    exact (c8FourRecordData770_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData771).card = 2 ^ c8FourRecordData771.generators.length
    rw [(c8FourRecordData771_rank_card).2]
    exact (c8FourRecordData771_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData772).card = 2 ^ c8FourRecordData772.generators.length
    rw [(c8FourRecordData772_rank_card).2]
    exact (c8FourRecordData772_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData773).card = 2 ^ c8FourRecordData773.generators.length
    rw [(c8FourRecordData773_rank_card).2]
    exact (c8FourRecordData773_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData774).card = 2 ^ c8FourRecordData774.generators.length
    rw [(c8FourRecordData774_rank_card).2]
    exact (c8FourRecordData774_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData775).card = 2 ^ c8FourRecordData775.generators.length
    rw [(c8FourRecordData775_rank_card).2]
    exact (c8FourRecordData775_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData776).card = 2 ^ c8FourRecordData776.generators.length
    rw [(c8FourRecordData776_rank_card).2]
    exact (c8FourRecordData776_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData777).card = 2 ^ c8FourRecordData777.generators.length
    rw [(c8FourRecordData777_rank_card).2]
    exact (c8FourRecordData777_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData778).card = 2 ^ c8FourRecordData778.generators.length
    rw [(c8FourRecordData778_rank_card).2]
    exact (c8FourRecordData778_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData779).card = 2 ^ c8FourRecordData779.generators.length
    rw [(c8FourRecordData779_rank_card).2]
    exact (c8FourRecordData779_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData780).card = 2 ^ c8FourRecordData780.generators.length
    rw [(c8FourRecordData780_rank_card).2]
    exact (c8FourRecordData780_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData781).card = 2 ^ c8FourRecordData781.generators.length
    rw [(c8FourRecordData781_rank_card).2]
    exact (c8FourRecordData781_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData782).card = 2 ^ c8FourRecordData782.generators.length
    rw [(c8FourRecordData782_rank_card).2]
    exact (c8FourRecordData782_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData783).card = 2 ^ c8FourRecordData783.generators.length
    rw [(c8FourRecordData783_rank_card).2]
    exact (c8FourRecordData783_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData784).card = 2 ^ c8FourRecordData784.generators.length
    rw [(c8FourRecordData784_rank_card).2]
    exact (c8FourRecordData784_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData785).card = 2 ^ c8FourRecordData785.generators.length
    rw [(c8FourRecordData785_rank_card).2]
    exact (c8FourRecordData785_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData786).card = 2 ^ c8FourRecordData786.generators.length
    rw [(c8FourRecordData786_rank_card).2]
    exact (c8FourRecordData786_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData787).card = 2 ^ c8FourRecordData787.generators.length
    rw [(c8FourRecordData787_rank_card).2]
    exact (c8FourRecordData787_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData788).card = 2 ^ c8FourRecordData788.generators.length
    rw [(c8FourRecordData788_rank_card).2]
    exact (c8FourRecordData788_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData789).card = 2 ^ c8FourRecordData789.generators.length
    rw [(c8FourRecordData789_rank_card).2]
    exact (c8FourRecordData789_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData790).card = 2 ^ c8FourRecordData790.generators.length
    rw [(c8FourRecordData790_rank_card).2]
    exact (c8FourRecordData790_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData791).card = 2 ^ c8FourRecordData791.generators.length
    rw [(c8FourRecordData791_rank_card).2]
    exact (c8FourRecordData791_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData792).card = 2 ^ c8FourRecordData792.generators.length
    rw [(c8FourRecordData792_rank_card).2]
    exact (c8FourRecordData792_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData793).card = 2 ^ c8FourRecordData793.generators.length
    rw [(c8FourRecordData793_rank_card).2]
    exact (c8FourRecordData793_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData794).card = 2 ^ c8FourRecordData794.generators.length
    rw [(c8FourRecordData794_rank_card).2]
    exact (c8FourRecordData794_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData795).card = 2 ^ c8FourRecordData795.generators.length
    rw [(c8FourRecordData795_rank_card).2]
    exact (c8FourRecordData795_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData796).card = 2 ^ c8FourRecordData796.generators.length
    rw [(c8FourRecordData796_rank_card).2]
    exact (c8FourRecordData796_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData797).card = 2 ^ c8FourRecordData797.generators.length
    rw [(c8FourRecordData797_rank_card).2]
    exact (c8FourRecordData797_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData798).card = 2 ^ c8FourRecordData798.generators.length
    rw [(c8FourRecordData798_rank_card).2]
    exact (c8FourRecordData798_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData799).card = 2 ^ c8FourRecordData799.generators.length
    rw [(c8FourRecordData799_rank_card).2]
    exact (c8FourRecordData799_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData800).card = 2 ^ c8FourRecordData800.generators.length
    rw [(c8FourRecordData800_rank_card).2]
    exact (c8FourRecordData800_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData801).card = 2 ^ c8FourRecordData801.generators.length
    rw [(c8FourRecordData801_rank_card).2]
    exact (c8FourRecordData801_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData802).card = 2 ^ c8FourRecordData802.generators.length
    rw [(c8FourRecordData802_rank_card).2]
    exact (c8FourRecordData802_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData803).card = 2 ^ c8FourRecordData803.generators.length
    rw [(c8FourRecordData803_rank_card).2]
    exact (c8FourRecordData803_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData804).card = 2 ^ c8FourRecordData804.generators.length
    rw [(c8FourRecordData804_rank_card).2]
    exact (c8FourRecordData804_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData805).card = 2 ^ c8FourRecordData805.generators.length
    rw [(c8FourRecordData805_rank_card).2]
    exact (c8FourRecordData805_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData806).card = 2 ^ c8FourRecordData806.generators.length
    rw [(c8FourRecordData806_rank_card).2]
    exact (c8FourRecordData806_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData807).card = 2 ^ c8FourRecordData807.generators.length
    rw [(c8FourRecordData807_rank_card).2]
    exact (c8FourRecordData807_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData808).card = 2 ^ c8FourRecordData808.generators.length
    rw [(c8FourRecordData808_rank_card).2]
    exact (c8FourRecordData808_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData809).card = 2 ^ c8FourRecordData809.generators.length
    rw [(c8FourRecordData809_rank_card).2]
    exact (c8FourRecordData809_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData810).card = 2 ^ c8FourRecordData810.generators.length
    rw [(c8FourRecordData810_rank_card).2]
    exact (c8FourRecordData810_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData811).card = 2 ^ c8FourRecordData811.generators.length
    rw [(c8FourRecordData811_rank_card).2]
    exact (c8FourRecordData811_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData812).card = 2 ^ c8FourRecordData812.generators.length
    rw [(c8FourRecordData812_rank_card).2]
    exact (c8FourRecordData812_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData813).card = 2 ^ c8FourRecordData813.generators.length
    rw [(c8FourRecordData813_rank_card).2]
    exact (c8FourRecordData813_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData814).card = 2 ^ c8FourRecordData814.generators.length
    rw [(c8FourRecordData814_rank_card).2]
    exact (c8FourRecordData814_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData815).card = 2 ^ c8FourRecordData815.generators.length
    rw [(c8FourRecordData815_rank_card).2]
    exact (c8FourRecordData815_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData816).card = 2 ^ c8FourRecordData816.generators.length
    rw [(c8FourRecordData816_rank_card).2]
    exact (c8FourRecordData816_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData817).card = 2 ^ c8FourRecordData817.generators.length
    rw [(c8FourRecordData817_rank_card).2]
    exact (c8FourRecordData817_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData818).card = 2 ^ c8FourRecordData818.generators.length
    rw [(c8FourRecordData818_rank_card).2]
    exact (c8FourRecordData818_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData819).card = 2 ^ c8FourRecordData819.generators.length
    rw [(c8FourRecordData819_rank_card).2]
    exact (c8FourRecordData819_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData820).card = 2 ^ c8FourRecordData820.generators.length
    rw [(c8FourRecordData820_rank_card).2]
    exact (c8FourRecordData820_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData821).card = 2 ^ c8FourRecordData821.generators.length
    rw [(c8FourRecordData821_rank_card).2]
    exact (c8FourRecordData821_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData822).card = 2 ^ c8FourRecordData822.generators.length
    rw [(c8FourRecordData822_rank_card).2]
    exact (c8FourRecordData822_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData823).card = 2 ^ c8FourRecordData823.generators.length
    rw [(c8FourRecordData823_rank_card).2]
    exact (c8FourRecordData823_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData824).card = 2 ^ c8FourRecordData824.generators.length
    rw [(c8FourRecordData824_rank_card).2]
    exact (c8FourRecordData824_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData825).card = 2 ^ c8FourRecordData825.generators.length
    rw [(c8FourRecordData825_rank_card).2]
    exact (c8FourRecordData825_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData826).card = 2 ^ c8FourRecordData826.generators.length
    rw [(c8FourRecordData826_rank_card).2]
    exact (c8FourRecordData826_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData827).card = 2 ^ c8FourRecordData827.generators.length
    rw [(c8FourRecordData827_rank_card).2]
    exact (c8FourRecordData827_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData828).card = 2 ^ c8FourRecordData828.generators.length
    rw [(c8FourRecordData828_rank_card).2]
    exact (c8FourRecordData828_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData829).card = 2 ^ c8FourRecordData829.generators.length
    rw [(c8FourRecordData829_rank_card).2]
    exact (c8FourRecordData829_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData830).card = 2 ^ c8FourRecordData830.generators.length
    rw [(c8FourRecordData830_rank_card).2]
    exact (c8FourRecordData830_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData831).card = 2 ^ c8FourRecordData831.generators.length
    rw [(c8FourRecordData831_rank_card).2]
    exact (c8FourRecordData831_rank_card).1

end CFSG.LargeEvenClassification.Helpers
