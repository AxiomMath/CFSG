
module

public import CFSG.Literature.GL52BFS
public import CFSG.Literature.GL52Elements
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.Literature.GL52IsosInputs
public import CFSG.Literature.GL52Pass
public meta import CFSG.Literature.GL52Pass

public section

namespace CFSG.Literature.GL52

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native

@[expose] def wordsE : List (List ℤ) :=
  [[], [4], [3], [3, 4], [2], [2, 4], [2, 3], [2, 3, 4], [1], [1, 4], [1, 3], [1, 3, 4], [1, 2],
    [1, 2, 4], [1, 2, 3], [1, 2, 3, 4]]

@[expose] def gensY : List G := [glS7, glFr]

@[expose] def wordsY : List (List ℤ) :=
  [[], [1], [2], [-1], [-2], [1, 1], [1, 2], [1, -2], [2, 1], [2, -1], [-1, 2], [-1, -1],
    [-1, -2], [-2, 1], [-2, -1], [1, 1, 1], [1, 1, -2], [1, 2, 1], [1, -2, 1], [2, 1, 1],
    [-1, -1, -1]]

abbrev wT (gs : List G) (w : List ℤ) : Table :=
  wordT 31 (letterT (genTables gs) (genInvTables gs)) w

end CFSG.Literature.GL52
