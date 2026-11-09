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
    .mul 0 1 3, .mul 3 1 4, .pow 2 3 5, .pow 2 4 6, .mul 5 6 7, .mul 7 3 8, .mul 7 4 9,
    .mul 8 9 10, .mul 10 8 31, .pow 2 31 11, .pow 2 11 12, .pow 2 12 32, .mul 0 32 33,
    .mul 33 0 34, .pow 2 34 35, .mul 32 35 36]

end CFSG.RankThree.PartOne.CTP.Fus
