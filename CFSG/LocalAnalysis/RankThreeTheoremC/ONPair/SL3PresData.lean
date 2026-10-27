module

public import CFSG.ClassicalInvolution.Phan.Phan3AData
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort
public import Mathlib

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.CosetTable CFSG.ClassicalInvolution.Phan.Q3G

@[expose] def sl3Codes7 : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 3, 0, 0, 3, 0, 0, 3, 0],
   [0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0],
   [0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 1],
   [4, 4, 4, 4, 4, 4, 4],
   [0, 4, 1, 5, 0, 4, 1, 5, 0, 4, 1, 5, 0, 4, 1, 5, 0, 4, 1, 5, 0, 4, 1, 5, 0, 4, 1, 5],
   [0, 0, 4, 1, 5, 1, 4, 0, 5, 1], [2, 4, 3, 5], [4, 0, 4, 1, 5, 0, 5, 1],
   [2, 0, 4, 1, 5, 3, 4, 0, 5, 1, 5], [6, 6, 6, 6, 6, 6, 6],
   [6, 2, 7, 3, 6, 2, 7, 3, 6, 2, 7, 3, 6, 2, 7, 3, 6, 2, 7, 3, 6, 2, 7, 3, 6, 2, 7, 3],
   [0, 6, 1, 7], [2, 6, 2, 7, 3, 6, 3, 7], [6, 6, 2, 7, 3, 7, 2, 6, 3, 7],
   [4, 6, 2, 7, 3, 5, 2, 6, 3, 7, 3], [6, 2, 7, 3, 0, 2, 6, 3, 7, 1, 7],
   [0, 4, 1, 5, 6, 4, 0, 5, 1, 7, 1]]

@[expose] def sl3Rels7 : List (List (Fin 4 × Bool)) := sl3Codes7.map (decodeWord 4)

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
