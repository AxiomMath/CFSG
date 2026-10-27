module

public import CFSG.RankThree.PartOne.CTP.FusionDefs

public section

namespace CFSG.RankThree.PartOne.CTP.Fus

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def betaMcLP3 : Spec where
  p := 3
  rA := 0
  oA := 2
  rB := 1
  oB := 5
  rx := 43
  ry := 69
  tx := 0
  gens := [
    ⟨0, 2, [(43, 1)], [(43, 1)], 0⟩,
    ⟨1, 5, [(69, 1)], [(69, 1)], 0⟩]
  wA := [(0, 1)]
  wB := [(1, 1)]

@[expose] def betaMcLP3N : Nat := 70

@[expose] def betaMcLP3Prog : List Op := [
    .pow 4 1 2, .mul 2 1 3, .mul 3 0 4, .mul 4 1 5, .mul 5 2 6, .mul 6 2 7, .mul 7 1 8,
    .mul 8 2 9, .mul 9 2 10, .pow 4 10 11, .mul 0 1 12, .mul 2 12 13, .mul 0 13 14,
    .mul 2 14 15, .mul 0 15 16, .mul 2 16 17, .mul 2 17 18, .mul 0 18 19, .mul 1 19 20,
    .mul 0 20 21, .mul 1 21 22, .mul 1 22 23, .mul 0 23 24, .mul 1 24 25, .mul 1 25 26,
    .mul 2 0 27, .mul 27 1 28, .mul 28 0 29, .mul 29 1 30, .mul 30 0 31, .mul 31 1 32,
    .mul 32 1 33, .mul 33 0 34, .mul 34 2 35, .mul 35 0 36, .mul 36 2 37, .mul 37 2 38,
    .mul 38 0 39, .mul 39 2 40, .mul 40 2 41, .mul 26 11 42, .mul 42 41 43, .mul 0 2 44,
    .mul 1 44 45, .mul 0 45 46, .mul 1 46 47, .mul 0 47 48, .mul 2 48 49, .mul 0 49 50,
    .mul 2 50 51, .mul 0 51 52, .mul 1 52 53, .mul 1 53 54, .mul 0 54 55, .mul 1 0 56,
    .mul 56 2 57, .mul 57 0 58, .mul 58 2 59, .mul 59 0 60, .mul 60 1 61, .mul 61 0 62,
    .mul 62 1 63, .mul 63 0 64, .mul 64 2 65, .mul 65 2 66, .mul 66 0 67, .mul 55 11 68,
    .mul 68 67 69]

end CFSG.RankThree.PartOne.CTP.Fus
