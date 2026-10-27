module

public import CFSG.RankThree.PartOne.CTP.FusionDefs

public section

namespace CFSG.RankThree.PartOne.CTP.Fus

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def betaJ3P3 : Spec where
  p := 3
  rA := 0
  oA := 2
  rB := 1
  oB := 3
  rx := 50
  ry := 68
  tx := 0
  gens := [
    ⟨0, 2, [(50, 1)], [(50, 1)], 0⟩,
    ⟨1, 3, [(68, 1)], [(68, 1)], 0⟩]
  wA := [(0, 1)]
  wB := [(1, 1)]

@[expose] def betaJ3P3N : Nat := 69

@[expose] def betaJ3P3Prog : List Op := [
    .pow 2 1 2, .mul 2 0 3, .mul 0 1 4, .mul 4 0 5, .mul 5 1 6, .mul 6 0 7, .mul 7 1 8,
    .mul 8 3 9, .mul 5 2 10, .mul 10 9 11, .mul 0 2 12, .mul 12 0 13, .mul 13 1 14,
    .mul 14 11 15, .mul 1 0 16, .mul 16 1 17, .mul 17 0 18, .mul 18 1 19, .mul 19 15 20,
    .mul 3 2 21, .mul 21 0 22, .mul 22 20 23, .mul 7 23 24, .mul 16 2 25, .mul 25 0 26,
    .mul 26 2 27, .mul 27 0 28, .mul 28 24 29, .mul 13 2 30, .mul 30 0 31, .mul 31 1 32,
    .mul 32 29 33, .mul 22 2 34, .mul 34 0 35, .mul 4 35 36, .mul 36 26 37, .mul 3 1 38,
    .mul 38 0 39, .mul 37 39 40, .mul 40 34 41, .mul 41 6 42, .mul 42 31 43, .mul 7 2 44,
    .mul 43 44 45, .mul 39 1 46, .mul 46 0 47, .mul 45 47 48, .mul 33 1 49, .mul 49 48 50,
    .mul 19 13 51, .mul 44 51 52, .mul 2 52 53, .mul 16 53 54, .mul 14 54 55, .mul 14 55 56,
    .mul 8 56 57, .mul 14 57 58, .mul 5 34 59, .mul 59 28 60, .mul 60 1 61, .mul 61 12 62,
    .mul 62 39 63, .mul 63 39 64, .mul 64 35 65, .mul 65 39 66, .mul 58 1 67, .mul 67 66 68]

end CFSG.RankThree.PartOne.CTP.Fus
