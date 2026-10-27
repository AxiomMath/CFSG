module

public import CFSG.RankThree.PartOne.CTP.FusionDefs

public section

namespace CFSG.RankThree.PartOne.CTP.Fus

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def betaSuzP3 : Spec where
  p := 3
  rA := 0
  oA := 2
  rB := 1
  oB := 3
  rx := 55
  ry := 131
  tx := 0
  gens := [
    ⟨0, 2, [(55, 1)], [(55, 2)], 0⟩,
    ⟨1, 3, [(131, 1)], [(131, 1)], 0⟩]
  wA := [(0, 1)]
  wB := [(1, 1)]

@[expose] def betaSuzP3N : Nat := 132

@[expose] def betaSuzP3Prog : List Op := [
    .pow 2 1 2, .mul 0 0 3, .mul 3 0 4, .mul 4 0 5, .mul 5 0 6, .mul 6 2 7, .mul 7 0 8,
    .pow 2 8 9, .mul 0 2 10, .mul 2 10 11, .mul 0 11 12, .mul 1 12 13, .mul 0 13 14,
    .mul 1 14 15, .mul 0 15 16, .mul 2 16 17, .mul 0 17 18, .mul 2 18 19, .mul 0 19 20,
    .mul 2 20 21, .mul 0 21 22, .mul 1 22 23, .mul 0 23 24, .mul 1 24 25, .mul 0 25 26,
    .mul 2 26 27, .mul 0 27 28, .mul 2 28 29, .mul 0 29 30, .mul 2 30 31, .mul 1 0 32,
    .mul 32 1 33, .mul 33 0 34, .mul 34 2 35, .mul 35 0 36, .mul 36 2 37, .mul 37 0 38,
    .mul 38 1 39, .mul 39 0 40, .mul 40 1 41, .mul 41 0 42, .mul 42 1 43, .mul 43 0 44,
    .mul 44 2 45, .mul 45 0 46, .mul 46 2 47, .mul 47 0 48, .mul 48 1 49, .mul 49 0 50,
    .mul 50 1 51, .mul 51 0 52, .mul 52 1 53, .mul 31 9 54, .mul 54 53 55, .mul 0 1 56,
    .mul 2 56 57, .mul 0 57 58, .mul 1 58 59, .mul 0 59 60, .mul 2 60 61, .mul 0 61 62,
    .mul 1 62 63, .mul 0 63 64, .mul 1 64 65, .mul 0 65 66, .mul 2 66 67, .mul 0 67 68,
    .mul 1 68 69, .mul 0 69 70, .mul 1 70 71, .mul 0 71 72, .mul 2 72 73, .mul 0 73 74,
    .mul 2 74 75, .mul 0 75 76, .mul 1 76 77, .mul 0 77 78, .mul 1 78 79, .mul 0 79 80,
    .mul 2 80 81, .mul 0 81 82, .mul 1 82 83, .mul 0 83 84, .mul 2 84 85, .mul 0 85 86,
    .mul 2 86 87, .mul 0 87 88, .mul 2 88 89, .mul 0 89 90, .mul 2 90 91, .mul 0 91 92,
    .mul 2 0 93, .mul 93 1 94, .mul 94 0 95, .mul 95 2 96, .mul 96 0 97, .mul 97 1 98,
    .mul 98 0 99, .mul 99 2 100, .mul 100 0 101, .mul 101 2 102, .mul 102 0 103,
    .mul 103 1 104, .mul 104 0 105, .mul 105 2 106, .mul 106 0 107, .mul 107 2 108,
    .mul 108 0 109, .mul 109 1 110, .mul 110 0 111, .mul 111 1 112, .mul 112 0 113,
    .mul 113 2 114, .mul 114 0 115, .mul 115 2 116, .mul 116 0 117, .mul 117 1 118,
    .mul 118 0 119, .mul 119 2 120, .mul 120 0 121, .mul 121 1 122, .mul 122 0 123,
    .mul 123 1 124, .mul 124 0 125, .mul 125 1 126, .mul 126 0 127, .mul 127 1 128,
    .mul 128 0 129, .mul 92 9 130, .mul 130 129 131]

end CFSG.RankThree.PartOne.CTP.Fus
