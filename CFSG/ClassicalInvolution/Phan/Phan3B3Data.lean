module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalInvolution.Phan.Phan3AData

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

@[expose] def b3SpCodes : List (List Nat) :=
  [[10, 10, 10], [5, 9, 4, 8], [8, 8, 8, 8], [4, 4, 4, 4], [5, 11, 4, 11, 8], [8, 4, 6, 9, 5, 7],
   [6, 4, 9, 7, 5, 8], [4, 7, 4, 7, 4, 7], [10, 6, 11, 4, 7, 10, 7, 11, 6, 5],
   [10, 7, 11, 7, 10, 7, 11, 6, 10, 6, 11, 6], [8, 10, 6, 11, 7, 11, 9, 7, 4, 10, 6, 11, 7, 4, 4]]

@[expose] def b3CommCodes : List (List Nat) :=
  [[0, 8, 1, 9], [0, 10, 1, 11], [2, 8, 3, 9], [2, 10, 3, 11]]

@[expose] def b3DefCodes : List (List Nat) :=
  [[13, 11, 9, 10, 4, 11, 8, 10], [15, 11, 9, 10, 6, 11, 8, 10]]

@[expose] def b3Comm11Codes : List (List Nat) :=
  [[4, 12, 5, 13], [4, 14, 5, 15], [6, 12, 7, 13], [6, 14, 7, 15]]

@[expose] def b3KerMap : Fin 6 → Fin 8 := ![2, 3, 0, 1, 6, 7]

@[expose] def b3KerWord (w : List (Fin 6 × Bool)) : List (Fin 8 × Bool) :=
  w.map fun l => (b3KerMap l.1, l.2)

@[expose] def b3RankTwoRels : List (List (Fin 8 × Bool)) :=
  (su3Codes ++ b3SpCodes ++ b3CommCodes ++ b3DefCodes ++ b3Comm11Codes).map (decodeWord 8)

@[expose] def phanB3Rels : List (List (Fin 8 × Bool)) :=
  b3RankTwoRels ++ [b3KerWord phanA3U1, b3KerWord phanA3U2]

end CFSG.ClassicalInvolution.Phan.Q3G
