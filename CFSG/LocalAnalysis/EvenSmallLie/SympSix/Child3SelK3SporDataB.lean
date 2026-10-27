module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3SporDefs
public import CFSG.Sporadic.SuzOddCore.Arrays
public import CFSG.Sporadic.Schreier.Co3Arrays
public import CFSG.Sporadic.Co2Cert.Data

public section

namespace CFSG.EvenSmallLie.Child3.SelK3

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.Co2Cert

@[expose] def suzK3Prog : String := include_str "Child3SelK3SporSuz.txt"

@[expose] def suzK3 : Data where
  n := 1782
  gens := #[b0Arr.map UInt32.ofNat, b1Arr.map UInt32.ofNat]
  regs := 74
  prog := parseProg suzK3Prog
  syl := [16, 28, 35]
  order := 2187
  reps :=
    [1125, 43, 655, 1064, 18, 638, 680, 939, 1356, 1635, 493, 398, 278, 1743, 476, 1275, 646, 616,
      702, 1532, 1070, 1249, 1351, 1361, 1560, 1639, 1690, 1719, 1746]
  wits :=
    [.v4 39 43, .z4 47, .v4 48 49, .v4 50 51, .z4 52, .z4 53, .z4 54, .v4 39 43, .z4 55, .z4 53,
      .v4 39 43, .v4 50 51, .v4 56 57, .z4 55, .v4 58 59, .v4 50 51, .v4 39 43, .v4 56 60,
      .v4 50 51, .z4 61, .v4 62 63, .v4 64 63, .z4 65, .v4 66 62, .v4 67 68, .v4 67 68, .v4 69 62,
      .v4 70 71, .v4 72 73]

@[expose] def co3K3Prog : String := include_str "Child3SelK3SporCo3.txt"

@[expose] def co3K3 : Data where
  n := 276
  gens := #[co3ChainArrs[0]!.map UInt32.ofNat, co3ChainArrs[1]!.map UInt32.ofNat]
  regs := 84
  prog := parseProg co3K3Prog
  syl := [31, 35, 37, 40]
  order := 2187
  reps :=
    [1646, 1234, 67, 357, 1504, 422, 11, 266, 2080, 797, 929, 542, 582, 429, 83, 1331, 197, 1614,
      1193, 2067, 524, 946, 566, 714, 881, 2121, 1322, 1173, 1971]
  wits :=
    [.v4 44 45, .z4 47, .z4 49, .v4 50 51, .v4 52 54, .z4 55, .z4 56, .v4 57 58, .v4 59 60, .z4 61,
      .v4 62 63, .z4 64, .v4 65 66, .v4 67 68, .v4 69 70, .v4 71 72, .z4 64, .z4 73, .z4 74, .z4 73,
      .z4 75, .z4 76, .z4 74, .v4 77 78, .v4 79 80, .v4 81 82, .z4 76, .z4 64, .z4 83]

@[expose] def co2K3Prog : String := include_str "Child3SelK3SporCo2.txt"

@[expose] def co2K3 : Data where
  n := 2300
  gens := #[co2OrigArrs[0]!.map UInt32.ofNat, co2OrigArrs[1]!.map UInt32.ofNat]
  regs := 74
  prog := parseProg co2K3Prog
  syl := [44, 45, 46]
  order := 729
  reps :=
    [113, 358, 153, 424, 263, 138, 93, 127, 192, 204, 208, 190, 277, 387, 406, 571, 402, 485, 688,
      652]
  wits :=
    [.v4 47 48, .v4 49 50, .v4 51 52, .v4 53 54, .v4 53 54, .v4 49 50, .v4 55 56, .z4 57, .v4 49 50,
      .z4 58, .v4 59 60, .v4 61 62, .v4 47 63, .v4 53 64, .v4 65 66, .v4 67 68, .v4 69 65,
      .v4 59 60, .v4 70 71, .v4 72 73]

end CFSG.EvenSmallLie.Child3.SelK3
