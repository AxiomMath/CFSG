module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.Y555Data

public section

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native

@[expose] def qW (i : ℕ) : List Native.Gen :=
  nodeW (5 * i + 1) ++ nodeW (5 * i + 2) ++ nodeW (5 * i + 3) ++ nodeW (5 * i + 4)

@[expose] def wW (i : ℕ) : List Native.Gen :=
  nodeW (5 * i + 1) ++ nodeW (5 * i + 3) ++ nodeW (5 * i + 4) ++ nodeW (5 * i + 3)

@[expose] def qOrderPairs : List (List Native.Gen × List Native.Gen) :=
  [0, 1, 2].map fun i => (powL 5 (qW i), [])

@[expose] def qCommPairs : List (List Native.Gen × List Native.Gen) :=
  [(0, 1), (0, 2), (1, 2)].map fun p => (qW p.2 ++ qW p.1, qW p.1 ++ qW p.2)

@[expose] def wInvPairs : List (List Native.Gen × List Native.Gen) :=
  [0, 1, 2].map fun i => (wW i ++ wW i, [])

@[expose] def wQSelfPairs : List (List Native.Gen × List Native.Gen) :=
  [0, 1, 2].map fun i => (wW i ++ qW i ++ wW i, powL 4 (qW i))

@[expose] def wQOtherPairs : List (List Native.Gen × List Native.Gen) :=
  [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)].map fun p =>
    (wW p.1 ++ qW p.2 ++ wW p.1, qW p.2)

@[expose] def nodeQPairs (a : ℕ) : List (List Native.Gen × List Native.Gen) :=
  ((List.range 5).flatMap fun k => [0, 1, 2].filterMap fun j =>
    if j = a then none else some (qW j ++ nodeW (5 * a + k), nodeW (5 * a + k) ++ qW j))

end CFSG.AGLEmbedding.Norton.MON5_7
