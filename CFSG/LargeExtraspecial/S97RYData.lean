module

public import CFSG.LargeExtraspecial.S97RYCheck
public import CFSG.CGT.Timmesfeld75.ListWCMathieuData

public section

namespace CFSG.LargeExtraspecial.S11.PairCheck

open CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75.WCCheck

@[expose] def a9tA : Table := #[1, 2, 0, 3, 4, 5, 6, 7, 8]

@[expose] def a9tAi : Table := #[2, 0, 1, 3, 4, 5, 6, 7, 8]

@[expose] def a9tB : Table := #[1, 2, 3, 4, 5, 6, 7, 8, 0]

@[expose] def a9tBi : Table := #[8, 0, 1, 2, 3, 4, 5, 6, 7]

@[expose] def a9gens (l : Int) : Table :=
  if l = 1 then a9tA else if l = -1 then a9tAi else if l = 2 then a9tB else
    if l = -2 then a9tBi else idT 9

@[expose] def a9pc : List (List Int) :=
    [[1, 2, -1, -2, 1], [1, -2, 1, 2, 2, 1, -2, -1, -2, 1, -2, -2, -2, 1, -2, 1], [1, 2, 1, -2],
    [-2, 1, 2, 2, -1, 2, 1, 2, 1, 2], [1, 2, -1, 2, 2, 2, -1, 2, -1, 2, 2, 2, 2, 1], [1, 2, 1, 2,
    2, 2, 1, 2, 1, 2, 2, 2, 2]]

@[expose] def a9cw : List (List Int) := [[-2, 1, 2, 2, 2]]

@[expose] def a9cls : List (List (Nat × List Int)) :=
    [[(4, []), (26, [-2, 1, 2, 2, 2]), (30, [-1, 2, -1, -2, -2, -2, -2, -1, 2]), (36, [-2, 1, 2,
    2, 1, 2, 2, 2]), (58, [-2, -2, -2, -1, 2]), (62, [2, 2, -1, 2, -1, -2, -2, -2])], [(6, []),
    (18, [-1, 2, -1, -2]), (20, [-2, -1, -2, -1, -2, 1, 2]), (38, [1, 2, 1, -2]), (50, [1, 2, -1,
    -2, 1]), (52, [-2, 1, 2, 2, 2])], [(12, []), (16, [2, 2, -1, 2, -1, -2, -2, -2]), (28, [1, 2,
    -1, -2, 1]), (44, [1, 2, 1, -2]), (48, [2, 2, 1, 2, -1, -2, 1, -2, -2]), (60, [-1, 2, -1,
    -2])]]

@[expose] def a9Data : Data where
  n := 9
  gens := a9gens
  pc := a9pc
  zIdx := 32
  cw := a9cw
  cls := a9cls
  verdicts := []

@[expose] def a9pv : List (List Bool × PVerdict) :=
    [([false, false, false], .size), ([false, false, true], .good [2] [] [1]), ([false, true,
    false], .good [1, 2] [] [1]), ([false, true, true], .size), ([true, false, false], .bad 4 32
    [-2, -2]), ([true, false, true], .size), ([true, true, false], .size), ([true, true, true],
    .size)]

@[expose] def a9PData : PData where
  D := a9Data
  ord := 8
  nCount := 0
  proper := true
  fuel := 64
  pv := a9pv

@[expose] def m22pv : List (List Bool × PVerdict) :=
  [([false, false], .size), ([false, true], .size), ([true, false], .size),
    ([true, true], .good [2, 2] [7, 31, 24] [])]

@[expose] def m22PData : PData where
  D := m22Data
  ord := 16
  nCount := 3
  proper := false
  fuel := 0
  pv := m22pv

end CFSG.LargeExtraspecial.S11.PairCheck
