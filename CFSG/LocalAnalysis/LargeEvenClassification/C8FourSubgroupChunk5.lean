module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupValid5
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupKernel5
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRank5

public section

namespace CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk5_valid (j : Fin 64) :
    c8FourRecordValid (c8FourRecordChunk5[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData320_valid
  · exact c8FourRecordData321_valid
  · exact c8FourRecordData322_valid
  · exact c8FourRecordData323_valid
  · exact c8FourRecordData324_valid
  · exact c8FourRecordData325_valid
  · exact c8FourRecordData326_valid
  · exact c8FourRecordData327_valid
  · exact c8FourRecordData328_valid
  · exact c8FourRecordData329_valid
  · exact c8FourRecordData330_valid
  · exact c8FourRecordData331_valid
  · exact c8FourRecordData332_valid
  · exact c8FourRecordData333_valid
  · exact c8FourRecordData334_valid
  · exact c8FourRecordData335_valid
  · exact c8FourRecordData336_valid
  · exact c8FourRecordData337_valid
  · exact c8FourRecordData338_valid
  · exact c8FourRecordData339_valid
  · exact c8FourRecordData340_valid
  · exact c8FourRecordData341_valid
  · exact c8FourRecordData342_valid
  · exact c8FourRecordData343_valid
  · exact c8FourRecordData344_valid
  · exact c8FourRecordData345_valid
  · exact c8FourRecordData346_valid
  · exact c8FourRecordData347_valid
  · exact c8FourRecordData348_valid
  · exact c8FourRecordData349_valid
  · exact c8FourRecordData350_valid
  · exact c8FourRecordData351_valid
  · exact c8FourRecordData352_valid
  · exact c8FourRecordData353_valid
  · exact c8FourRecordData354_valid
  · exact c8FourRecordData355_valid
  · exact c8FourRecordData356_valid
  · exact c8FourRecordData357_valid
  · exact c8FourRecordData358_valid
  · exact c8FourRecordData359_valid
  · exact c8FourRecordData360_valid
  · exact c8FourRecordData361_valid
  · exact c8FourRecordData362_valid
  · exact c8FourRecordData363_valid
  · exact c8FourRecordData364_valid
  · exact c8FourRecordData365_valid
  · exact c8FourRecordData366_valid
  · exact c8FourRecordData367_valid
  · exact c8FourRecordData368_valid
  · exact c8FourRecordData369_valid
  · exact c8FourRecordData370_valid
  · exact c8FourRecordData371_valid
  · exact c8FourRecordData372_valid
  · exact c8FourRecordData373_valid
  · exact c8FourRecordData374_valid
  · exact c8FourRecordData375_valid
  · exact c8FourRecordData376_valid
  · exact c8FourRecordData377_valid
  · exact c8FourRecordData378_valid
  · exact c8FourRecordData379_valid
  · exact c8FourRecordData380_valid
  · exact c8FourRecordData381_valid
  · exact c8FourRecordData382_valid
  · exact c8FourRecordData383_valid

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk5_kernels (j : Fin 64) :
    c8FourKernelListsValid (c8FourRecordChunk5[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData320_kernels
  · exact c8FourRecordData321_kernels
  · exact c8FourRecordData322_kernels
  · exact c8FourRecordData323_kernels
  · exact c8FourRecordData324_kernels
  · exact c8FourRecordData325_kernels
  · exact c8FourRecordData326_kernels
  · exact c8FourRecordData327_kernels
  · exact c8FourRecordData328_kernels
  · exact c8FourRecordData329_kernels
  · exact c8FourRecordData330_kernels
  · exact c8FourRecordData331_kernels
  · exact c8FourRecordData332_kernels
  · exact c8FourRecordData333_kernels
  · exact c8FourRecordData334_kernels
  · exact c8FourRecordData335_kernels
  · exact c8FourRecordData336_kernels
  · exact c8FourRecordData337_kernels
  · exact c8FourRecordData338_kernels
  · exact c8FourRecordData339_kernels
  · exact c8FourRecordData340_kernels
  · exact c8FourRecordData341_kernels
  · exact c8FourRecordData342_kernels
  · exact c8FourRecordData343_kernels
  · exact c8FourRecordData344_kernels
  · exact c8FourRecordData345_kernels
  · exact c8FourRecordData346_kernels
  · exact c8FourRecordData347_kernels
  · exact c8FourRecordData348_kernels
  · exact c8FourRecordData349_kernels
  · exact c8FourRecordData350_kernels
  · exact c8FourRecordData351_kernels
  · exact c8FourRecordData352_kernels
  · exact c8FourRecordData353_kernels
  · exact c8FourRecordData354_kernels
  · exact c8FourRecordData355_kernels
  · exact c8FourRecordData356_kernels
  · exact c8FourRecordData357_kernels
  · exact c8FourRecordData358_kernels
  · exact c8FourRecordData359_kernels
  · exact c8FourRecordData360_kernels
  · exact c8FourRecordData361_kernels
  · exact c8FourRecordData362_kernels
  · exact c8FourRecordData363_kernels
  · exact c8FourRecordData364_kernels
  · exact c8FourRecordData365_kernels
  · exact c8FourRecordData366_kernels
  · exact c8FourRecordData367_kernels
  · exact c8FourRecordData368_kernels
  · exact c8FourRecordData369_kernels
  · exact c8FourRecordData370_kernels
  · exact c8FourRecordData371_kernels
  · exact c8FourRecordData372_kernels
  · exact c8FourRecordData373_kernels
  · exact c8FourRecordData374_kernels
  · exact c8FourRecordData375_kernels
  · exact c8FourRecordData376_kernels
  · exact c8FourRecordData377_kernels
  · exact c8FourRecordData378_kernels
  · exact c8FourRecordData379_kernels
  · exact c8FourRecordData380_kernels
  · exact c8FourRecordData381_kernels
  · exact c8FourRecordData382_kernels
  · exact c8FourRecordData383_kernels

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk5_vectors (j : Fin 64) :
    c8FourGeneratorVectorsValid (c8FourRecordChunk5[j.val]!) := by
  fin_cases j
  · exact c8FourRecordData320_vectors
  · exact c8FourRecordData321_vectors
  · exact c8FourRecordData322_vectors
  · exact c8FourRecordData323_vectors
  · exact c8FourRecordData324_vectors
  · exact c8FourRecordData325_vectors
  · exact c8FourRecordData326_vectors
  · exact c8FourRecordData327_vectors
  · exact c8FourRecordData328_vectors
  · exact c8FourRecordData329_vectors
  · exact c8FourRecordData330_vectors
  · exact c8FourRecordData331_vectors
  · exact c8FourRecordData332_vectors
  · exact c8FourRecordData333_vectors
  · exact c8FourRecordData334_vectors
  · exact c8FourRecordData335_vectors
  · exact c8FourRecordData336_vectors
  · exact c8FourRecordData337_vectors
  · exact c8FourRecordData338_vectors
  · exact c8FourRecordData339_vectors
  · exact c8FourRecordData340_vectors
  · exact c8FourRecordData341_vectors
  · exact c8FourRecordData342_vectors
  · exact c8FourRecordData343_vectors
  · exact c8FourRecordData344_vectors
  · exact c8FourRecordData345_vectors
  · exact c8FourRecordData346_vectors
  · exact c8FourRecordData347_vectors
  · exact c8FourRecordData348_vectors
  · exact c8FourRecordData349_vectors
  · exact c8FourRecordData350_vectors
  · exact c8FourRecordData351_vectors
  · exact c8FourRecordData352_vectors
  · exact c8FourRecordData353_vectors
  · exact c8FourRecordData354_vectors
  · exact c8FourRecordData355_vectors
  · exact c8FourRecordData356_vectors
  · exact c8FourRecordData357_vectors
  · exact c8FourRecordData358_vectors
  · exact c8FourRecordData359_vectors
  · exact c8FourRecordData360_vectors
  · exact c8FourRecordData361_vectors
  · exact c8FourRecordData362_vectors
  · exact c8FourRecordData363_vectors
  · exact c8FourRecordData364_vectors
  · exact c8FourRecordData365_vectors
  · exact c8FourRecordData366_vectors
  · exact c8FourRecordData367_vectors
  · exact c8FourRecordData368_vectors
  · exact c8FourRecordData369_vectors
  · exact c8FourRecordData370_vectors
  · exact c8FourRecordData371_vectors
  · exact c8FourRecordData372_vectors
  · exact c8FourRecordData373_vectors
  · exact c8FourRecordData374_vectors
  · exact c8FourRecordData375_vectors
  · exact c8FourRecordData376_vectors
  · exact c8FourRecordData377_vectors
  · exact c8FourRecordData378_vectors
  · exact c8FourRecordData379_vectors
  · exact c8FourRecordData380_vectors
  · exact c8FourRecordData381_vectors
  · exact c8FourRecordData382_vectors
  · exact c8FourRecordData383_vectors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem c8Four_chunk5_rank_cards (j : Fin 64) :
    (c8FourRecordBinaryImages (c8FourRecordChunk5[j.val]!)).card = 2 ^ (c8FourRecordChunk5[j.val]!).generators.length := by
  fin_cases j
  · change (c8FourRecordBinaryImages c8FourRecordData320).card = 2 ^ c8FourRecordData320.generators.length
    rw [(c8FourRecordData320_rank_card).2]
    exact (c8FourRecordData320_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData321).card = 2 ^ c8FourRecordData321.generators.length
    rw [(c8FourRecordData321_rank_card).2]
    exact (c8FourRecordData321_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData322).card = 2 ^ c8FourRecordData322.generators.length
    rw [(c8FourRecordData322_rank_card).2]
    exact (c8FourRecordData322_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData323).card = 2 ^ c8FourRecordData323.generators.length
    rw [(c8FourRecordData323_rank_card).2]
    exact (c8FourRecordData323_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData324).card = 2 ^ c8FourRecordData324.generators.length
    rw [(c8FourRecordData324_rank_card).2]
    exact (c8FourRecordData324_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData325).card = 2 ^ c8FourRecordData325.generators.length
    rw [(c8FourRecordData325_rank_card).2]
    exact (c8FourRecordData325_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData326).card = 2 ^ c8FourRecordData326.generators.length
    rw [(c8FourRecordData326_rank_card).2]
    exact (c8FourRecordData326_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData327).card = 2 ^ c8FourRecordData327.generators.length
    rw [(c8FourRecordData327_rank_card).2]
    exact (c8FourRecordData327_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData328).card = 2 ^ c8FourRecordData328.generators.length
    rw [(c8FourRecordData328_rank_card).2]
    exact (c8FourRecordData328_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData329).card = 2 ^ c8FourRecordData329.generators.length
    rw [(c8FourRecordData329_rank_card).2]
    exact (c8FourRecordData329_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData330).card = 2 ^ c8FourRecordData330.generators.length
    rw [(c8FourRecordData330_rank_card).2]
    exact (c8FourRecordData330_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData331).card = 2 ^ c8FourRecordData331.generators.length
    rw [(c8FourRecordData331_rank_card).2]
    exact (c8FourRecordData331_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData332).card = 2 ^ c8FourRecordData332.generators.length
    rw [(c8FourRecordData332_rank_card).2]
    exact (c8FourRecordData332_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData333).card = 2 ^ c8FourRecordData333.generators.length
    rw [(c8FourRecordData333_rank_card).2]
    exact (c8FourRecordData333_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData334).card = 2 ^ c8FourRecordData334.generators.length
    rw [(c8FourRecordData334_rank_card).2]
    exact (c8FourRecordData334_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData335).card = 2 ^ c8FourRecordData335.generators.length
    rw [(c8FourRecordData335_rank_card).2]
    exact (c8FourRecordData335_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData336).card = 2 ^ c8FourRecordData336.generators.length
    rw [(c8FourRecordData336_rank_card).2]
    exact (c8FourRecordData336_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData337).card = 2 ^ c8FourRecordData337.generators.length
    rw [(c8FourRecordData337_rank_card).2]
    exact (c8FourRecordData337_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData338).card = 2 ^ c8FourRecordData338.generators.length
    rw [(c8FourRecordData338_rank_card).2]
    exact (c8FourRecordData338_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData339).card = 2 ^ c8FourRecordData339.generators.length
    rw [(c8FourRecordData339_rank_card).2]
    exact (c8FourRecordData339_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData340).card = 2 ^ c8FourRecordData340.generators.length
    rw [(c8FourRecordData340_rank_card).2]
    exact (c8FourRecordData340_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData341).card = 2 ^ c8FourRecordData341.generators.length
    rw [(c8FourRecordData341_rank_card).2]
    exact (c8FourRecordData341_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData342).card = 2 ^ c8FourRecordData342.generators.length
    rw [(c8FourRecordData342_rank_card).2]
    exact (c8FourRecordData342_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData343).card = 2 ^ c8FourRecordData343.generators.length
    rw [(c8FourRecordData343_rank_card).2]
    exact (c8FourRecordData343_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData344).card = 2 ^ c8FourRecordData344.generators.length
    rw [(c8FourRecordData344_rank_card).2]
    exact (c8FourRecordData344_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData345).card = 2 ^ c8FourRecordData345.generators.length
    rw [(c8FourRecordData345_rank_card).2]
    exact (c8FourRecordData345_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData346).card = 2 ^ c8FourRecordData346.generators.length
    rw [(c8FourRecordData346_rank_card).2]
    exact (c8FourRecordData346_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData347).card = 2 ^ c8FourRecordData347.generators.length
    rw [(c8FourRecordData347_rank_card).2]
    exact (c8FourRecordData347_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData348).card = 2 ^ c8FourRecordData348.generators.length
    rw [(c8FourRecordData348_rank_card).2]
    exact (c8FourRecordData348_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData349).card = 2 ^ c8FourRecordData349.generators.length
    rw [(c8FourRecordData349_rank_card).2]
    exact (c8FourRecordData349_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData350).card = 2 ^ c8FourRecordData350.generators.length
    rw [(c8FourRecordData350_rank_card).2]
    exact (c8FourRecordData350_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData351).card = 2 ^ c8FourRecordData351.generators.length
    rw [(c8FourRecordData351_rank_card).2]
    exact (c8FourRecordData351_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData352).card = 2 ^ c8FourRecordData352.generators.length
    rw [(c8FourRecordData352_rank_card).2]
    exact (c8FourRecordData352_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData353).card = 2 ^ c8FourRecordData353.generators.length
    rw [(c8FourRecordData353_rank_card).2]
    exact (c8FourRecordData353_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData354).card = 2 ^ c8FourRecordData354.generators.length
    rw [(c8FourRecordData354_rank_card).2]
    exact (c8FourRecordData354_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData355).card = 2 ^ c8FourRecordData355.generators.length
    rw [(c8FourRecordData355_rank_card).2]
    exact (c8FourRecordData355_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData356).card = 2 ^ c8FourRecordData356.generators.length
    rw [(c8FourRecordData356_rank_card).2]
    exact (c8FourRecordData356_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData357).card = 2 ^ c8FourRecordData357.generators.length
    rw [(c8FourRecordData357_rank_card).2]
    exact (c8FourRecordData357_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData358).card = 2 ^ c8FourRecordData358.generators.length
    rw [(c8FourRecordData358_rank_card).2]
    exact (c8FourRecordData358_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData359).card = 2 ^ c8FourRecordData359.generators.length
    rw [(c8FourRecordData359_rank_card).2]
    exact (c8FourRecordData359_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData360).card = 2 ^ c8FourRecordData360.generators.length
    rw [(c8FourRecordData360_rank_card).2]
    exact (c8FourRecordData360_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData361).card = 2 ^ c8FourRecordData361.generators.length
    rw [(c8FourRecordData361_rank_card).2]
    exact (c8FourRecordData361_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData362).card = 2 ^ c8FourRecordData362.generators.length
    rw [(c8FourRecordData362_rank_card).2]
    exact (c8FourRecordData362_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData363).card = 2 ^ c8FourRecordData363.generators.length
    rw [(c8FourRecordData363_rank_card).2]
    exact (c8FourRecordData363_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData364).card = 2 ^ c8FourRecordData364.generators.length
    rw [(c8FourRecordData364_rank_card).2]
    exact (c8FourRecordData364_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData365).card = 2 ^ c8FourRecordData365.generators.length
    rw [(c8FourRecordData365_rank_card).2]
    exact (c8FourRecordData365_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData366).card = 2 ^ c8FourRecordData366.generators.length
    rw [(c8FourRecordData366_rank_card).2]
    exact (c8FourRecordData366_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData367).card = 2 ^ c8FourRecordData367.generators.length
    rw [(c8FourRecordData367_rank_card).2]
    exact (c8FourRecordData367_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData368).card = 2 ^ c8FourRecordData368.generators.length
    rw [(c8FourRecordData368_rank_card).2]
    exact (c8FourRecordData368_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData369).card = 2 ^ c8FourRecordData369.generators.length
    rw [(c8FourRecordData369_rank_card).2]
    exact (c8FourRecordData369_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData370).card = 2 ^ c8FourRecordData370.generators.length
    rw [(c8FourRecordData370_rank_card).2]
    exact (c8FourRecordData370_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData371).card = 2 ^ c8FourRecordData371.generators.length
    rw [(c8FourRecordData371_rank_card).2]
    exact (c8FourRecordData371_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData372).card = 2 ^ c8FourRecordData372.generators.length
    rw [(c8FourRecordData372_rank_card).2]
    exact (c8FourRecordData372_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData373).card = 2 ^ c8FourRecordData373.generators.length
    rw [(c8FourRecordData373_rank_card).2]
    exact (c8FourRecordData373_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData374).card = 2 ^ c8FourRecordData374.generators.length
    rw [(c8FourRecordData374_rank_card).2]
    exact (c8FourRecordData374_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData375).card = 2 ^ c8FourRecordData375.generators.length
    rw [(c8FourRecordData375_rank_card).2]
    exact (c8FourRecordData375_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData376).card = 2 ^ c8FourRecordData376.generators.length
    rw [(c8FourRecordData376_rank_card).2]
    exact (c8FourRecordData376_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData377).card = 2 ^ c8FourRecordData377.generators.length
    rw [(c8FourRecordData377_rank_card).2]
    exact (c8FourRecordData377_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData378).card = 2 ^ c8FourRecordData378.generators.length
    rw [(c8FourRecordData378_rank_card).2]
    exact (c8FourRecordData378_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData379).card = 2 ^ c8FourRecordData379.generators.length
    rw [(c8FourRecordData379_rank_card).2]
    exact (c8FourRecordData379_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData380).card = 2 ^ c8FourRecordData380.generators.length
    rw [(c8FourRecordData380_rank_card).2]
    exact (c8FourRecordData380_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData381).card = 2 ^ c8FourRecordData381.generators.length
    rw [(c8FourRecordData381_rank_card).2]
    exact (c8FourRecordData381_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData382).card = 2 ^ c8FourRecordData382.generators.length
    rw [(c8FourRecordData382_rank_card).2]
    exact (c8FourRecordData382_rank_card).1
  · change (c8FourRecordBinaryImages c8FourRecordData383).card = 2 ^ c8FourRecordData383.generators.length
    rw [(c8FourRecordData383_rank_card).2]
    exact (c8FourRecordData383_rank_card).1

end CFSG.LargeEvenClassification.Helpers
