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

end CFSG.AGLEmbedding.Norton.MON5_7
