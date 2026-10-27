module

public import CFSG.RankThree.PartOne.CTP.FusionDefs

public section

namespace CFSG.RankThree.PartOne.CTP.Fus

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def betaCo3P3 : Spec where
  p := 3
  rA := 0
  oA := 3
  rB := 1
  oB := 4
  rx := 10
  ry := 44
  tx := 0
  gens := [
    ⟨0, 3, [(10, 1)], [(10, 1)], 0⟩,
    ⟨1, 4, [(44, 1)], [(44, 1)], 0⟩]
  wA := [(0, 1)]
  wB := [(1, 1)]

@[expose] def betaCo3P3N : Nat := 45

@[expose] def betaCo3P3Prog : List Op := [
    .pow 3 1 2, .pow 2 0 3, .mul 0 0 4, .mul 4 3 5, .mul 5 1 6, .mul 6 3 7, .mul 7 0 8,
    .mul 8 1 9, .pow 16 9 10, .mul 0 1 11, .mul 1 11 12, .mul 0 12 13, .mul 1 13 14,
    .mul 0 14 15, .mul 1 15 16, .mul 3 16 17, .mul 1 17 18, .mul 1 18 19, .mul 3 19 20,
    .mul 1 20 21, .mul 3 21 22, .mul 1 22 23, .mul 3 23 24, .mul 1 24 25, .mul 3 25 26,
    .mul 2 3 27, .mul 27 2 28, .mul 28 3 29, .mul 29 2 30, .mul 30 3 31, .mul 31 2 32,
    .mul 32 0 33, .mul 33 2 34, .mul 34 2 35, .mul 35 0 36, .mul 36 2 37, .mul 37 0 38,
    .mul 38 2 39, .mul 39 0 40, .mul 40 2 41, .mul 41 0 42, .mul 26 10 43, .mul 43 42 44]

end CFSG.RankThree.PartOne.CTP.Fus
