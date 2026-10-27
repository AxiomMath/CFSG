module

public import CFSG.RankThree.PartOne.CTP.FusionDefs

public section

namespace CFSG.RankThree.PartOne.CTP.Fus

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def betaFi24P3 : Spec where
  p := 3
  rA := 0
  oA := 2
  rB := 1
  oB := 3
  rx := 36
  ry := 32
  tx := 0
  gens := [
    ⟨0, 2, [(36, 1)], [(36, 2)], 0⟩,
    ⟨1, 3, [(32, 1)], [(32, 1)], 0⟩]
  wA := [(0, 1)]
  wB := [(1, 1)]

@[expose] def betaFi24P3N : Nat := 37

@[expose] def betaFi24P3Prog : List Op := [
    .pow 2 1 2, .mul 0 1 3, .mul 3 0 4, .mul 4 1 5, .mul 5 0 6, .mul 6 2 7, .mul 7 0 8,
    .mul 8 2 9, .mul 9 0 10, .mul 10 1 11, .mul 11 0 12, .mul 12 1 13, .mul 13 0 14,
    .mul 14 1 15, .mul 15 0 16, .mul 16 2 17, .mul 17 0 18, .mul 18 2 19, .mul 19 0 20,
    .mul 20 2 21, .mul 21 0 22, .mul 22 1 23, .mul 23 0 24, .mul 24 1 25, .mul 25 0 26,
    .mul 26 2 27, .mul 27 0 28, .mul 28 2 29, .mul 29 0 30, .mul 30 1 31, .pow 8 31 32,
    .mul 0 32 33, .mul 33 0 34, .pow 2 34 35, .mul 32 35 36]

end CFSG.RankThree.PartOne.CTP.Fus
