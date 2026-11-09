module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.ThreeBData
public import CFSG.YGroups.Y443.Native.Words

public section

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native

@[expose] def tbEntry (R : List (List ℕ)) (i j : ℕ) : ℕ := (R.getD i []).getD j 0

@[expose] def tbOrderPairs : List (List Native.Gen × List Native.Gen) :=
  (List.range 12).map fun i => (powL 3 (tbQ i), [])

@[expose] def tbWOrderPairs : List (List Native.Gen × List Native.Gen) :=
  [(powL 3 tbW, [])]

@[expose] def tbCentralPairs : List (List Native.Gen × List Native.Gen) :=
  (List.range 12).map fun i => (tbW ++ tbQ i, tbQ i ++ tbW)

@[expose] def tbChainPairs (is : List ℕ) : List (List Native.Gen × List Native.Gen) :=
  is.flatMap fun i => (List.range 12).filterMap fun j =>
    if i < j then
      some (tbQ j ++ tbQ i, tbQ i ++ powL (tbEntry tbMRows i j) tbW ++ tbQ j)
    else none

@[expose] def tbRowWord (R : List (List ℕ)) (i : ℕ) : List Native.Gen :=
  (((List.range 12).reverse).map fun j => powL (tbEntry R i j) (tbQ j)).flatten

@[expose] def tbActPairs (b : List Native.Gen) (R : List (List ℕ)) (c : List ℕ) (is : List ℕ) :
    List (List Native.Gen × List Native.Gen) :=
  is.map fun i => (b ++ tbQ i, powL (c.getD i 0) tbW ++ tbRowWord R i ++ b)

@[expose] def tbTreeWord (L : List ℕ) : List Native.Gen := (L.map tbQ).flatten

@[expose] def tbTreePairs (b : List Native.Gen) (T : List (List ℕ)) (c : List ℕ) (is : List ℕ) :
    List (List Native.Gen × List Native.Gen) :=
  is.map fun i => (b ++ tbQ i, tbTreeWord (T.getD i []) ++ powL (c.getD i 0) tbW ++ b)

@[expose] def tbXTree : List (List ℕ) :=
  [[11, 8, 8, 5, 4, 3, 3, 10, 9, 9, 6, 5, 2, 2, 1, 1, 10, 6], [11, 8, 8, 5, 4, 3, 3, 11, 4, 0],
    [11, 8, 8, 5, 4, 3, 3, 10, 9, 9, 6, 5, 2, 2, 1, 1, 11, 7, 4, 3, 0, 0],
    [10, 10, 5, 5, 2, 11, 9, 8, 8, 3, 2], [10, 10, 5, 5, 2, 6, 4, 4, 1, 11, 11, 7, 3],
    [10, 10, 5, 5, 2, 6, 4, 4, 1, 9, 9, 5], [11, 8, 7, 3, 2, 11, 4, 1, 0, 0, 9, 4, 2],
    [11, 8, 7, 3, 2, 11, 4, 1, 0, 0, 8, 7, 6, 3], [11, 8, 7, 3, 2, 10, 10, 7, 5, 3],
    [10, 6, 6, 3, 4, 2, 2, 1, 1, 7, 3, 8, 5, 10, 4],
    [10, 6, 6, 3, 4, 2, 2, 1, 1, 7, 7, 9, 11, 11, 5, 0, 0, 9],
    [10, 6, 6, 3, 4, 2, 2, 1, 1, 7, 7, 9, 11, 11]]

@[expose] def tbXTreeC : List ℕ := [0, 1, 2, 2, 2, 2, 1, 1, 1, 1, 0, 0]

@[expose] def tbYTree : List (List ℕ) :=
  [[0, 0], [0, 0, 6, 6, 2, 0, 5, 0, 8, 2, 1, 1], [0, 4, 4, 3, 0], [0, 0, 6, 6, 5, 5],
    [0, 4, 4, 3, 6, 5, 5], [0, 0, 6, 6, 2, 0], [0, 4, 4, 3, 6, 3, 2],
    [0, 0, 6, 6, 2, 0, 5, 0, 10, 0, 6, 4, 10, 7, 2, 8, 3, 3, 2], [0, 0, 6, 6, 2, 0, 5, 0, 10, 0, 9],
    [0, 0, 6, 6, 2, 0, 5, 0, 10, 0, 6, 4, 10, 7, 2, 9, 7, 4],
    [0, 0, 6, 6, 2, 0, 5, 0, 10, 0, 6, 4, 11, 8, 8, 6, 3, 11, 4, 3, 0],
    [0, 0, 6, 6, 2, 0, 5, 0, 10, 0, 6, 4, 11, 8, 8, 6, 3, 9, 9, 7, 6, 5]]

@[expose] def tbYTreeC : List ℕ := [0, 0, 0, 1, 0, 0, 0, 0, 2, 2, 0, 1]

end CFSG.AGLEmbedding.Norton.MON5_7
