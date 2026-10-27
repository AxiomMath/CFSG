module

public import CFSG.RankThree.PartOne.CTP.FusionDefs

public section

namespace CFSG.RankThree.PartOne.CTP.Fus

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def fusD2HS : Spec where
  p := 3
  rA := 0
  oA := 2
  rB := 1
  oB := 5
  rx := 9
  ry := 33
  tx := 0
  gens :=
    [⟨47, 15, [(9, 1)], [(9, 1)], 0⟩, ⟨53, 6, [(9, 1), (33, 1)], [(9, 1), (33, 1)], 0⟩]
  wA :=
    [(47, 1), (53, 1), (47, 1), (47, 1), (53, 1), (53, 1), (47, 1), (53, 5), (47, 1), (53, 1),
     (47, 1), (47, 1), (47, 1), (53, 1), (47, 14), (53, 1), (47, 14), (47, 14), (53, 1)]
  wB :=
    [(53, 1), (47, 14), (53, 5), (53, 5), (47, 14), (53, 5), (47, 14), (47, 14), (53, 1), (47, 1),
     (47, 1), (47, 1), (53, 5), (47, 1), (47, 1), (53, 5), (47, 14), (53, 5), (53, 5)]

@[expose] def fusD2HSN : Nat := 54

@[expose] def fusD2HSProg : List Op :=
    [.pow 4 1 2, .mul 0 1 3, .mul 3 0 4, .mul 4 2 5, .mul 5 0 6, .mul 6 2 7, .mul 7 0 8,
     .mul 8 1 9, .mul 0 2 10, .mul 10 0 11, .mul 11 1 12, .mul 12 1 13, .mul 13 0 14,
     .mul 14 1 15, .mul 15 0 16, .mul 16 1 17, .mul 17 0 18, .mul 18 1 19, .mul 19 0 20,
     .mul 20 2 21, .mul 21 2 22, .mul 22 0 23, .mul 23 1 24, .mul 24 0 25, .mul 25 1 26,
     .mul 26 0 27, .mul 27 1 28, .mul 28 0 29, .mul 29 1 30, .mul 30 1 31, .mul 31 0 32,
     .mul 32 2 33, .mul 10 2 34, .mul 34 0 35, .mul 35 2 36, .mul 36 0 37, .mul 37 1 38,
     .mul 38 0 39, .mul 39 1 40, .mul 40 0 41, .mul 41 1 42, .mul 42 0 43, .mul 43 2 44,
     .mul 44 0 45, .mul 45 2 46, .mul 46 2 47, .mul 15 1 48, .mul 48 0 49, .mul 49 1 50,
     .mul 50 1 51, .mul 51 0 52, .mul 52 2 53]

end CFSG.RankThree.PartOne.CTP.Fus
