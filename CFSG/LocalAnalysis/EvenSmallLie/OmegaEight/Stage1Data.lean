module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParF2

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

inductive Eps
  | plus
  | minus
  deriving DecidableEq

@[expose] def qfB : Eps → ℕ → Bool
  | .plus, x => (x.testBit 0 && x.testBit 5) ^^ (x.testBit 1 && x.testBit 4) ^^
      (x.testBit 2 && x.testBit 3)
  | .minus, x => (x.testBit 0 && x.testBit 5) ^^ (x.testBit 1 && x.testBit 4) ^^ x.testBit 2 ^^
      (x.testBit 2 && x.testBit 3) ^^ x.testBit 3

@[expose] def bfB (ε : Eps) (x y : ℕ) : Bool := qfB ε (x ^^^ y) ^^ qfB ε x ^^ qfB ε y

@[expose] def id6 : Array ℕ := #[1, 2, 4, 8, 16, 32]

@[expose] def genRows : Eps → ℕ → Array ℕ
  | .plus, 0 => #[1, 16, 24, 20, 30, 32]
  | .plus, 1 => #[47, 62, 42, 38, 2, 32]
  | .plus, 2 => #[1, 31, 11, 7, 2, 47]
  | .plus, 3 => #[34, 51, 4, 8, 2, 3]
  | .plus, 4 => #[52, 16, 4, 61, 55, 21]
  | .plus, 5 => #[56, 16, 61, 8, 59, 25]
  | .minus, 0 => #[41, 2, 36, 8, 16, 32]
  | .minus, 1 => #[32, 2, 44, 8, 16, 41]
  | .minus, 2 => #[41, 23, 44, 29, 16, 53]
  | .minus, 3 => #[41, 26, 52, 8, 16, 32]
  | .minus, 4 => #[41, 2, 38, 8, 26, 32]
  | _, _ => id6

@[expose] def genInvRows : Eps → ℕ → Array ℕ
  | .plus, 0 => #[1, 30, 10, 6, 2, 32]
  | .plus, 1 => #[61, 16, 56, 52, 62, 32]
  | .plus, 2 => #[1, 16, 25, 21, 31, 61]
  | .plus, 3 => #[48, 16, 4, 8, 51, 17]
  | .plus, 4 => #[38, 55, 4, 47, 2, 7]
  | .plus, 5 => #[42, 59, 47, 8, 2, 11]
  | .minus, 0 => #[41, 2, 36, 8, 16, 32]
  | .minus, 1 => #[41, 2, 13, 8, 16, 1]
  | .minus, 2 => #[41, 23, 44, 29, 16, 53]
  | .minus, 3 => #[41, 26, 52, 8, 16, 32]
  | .minus, 4 => #[41, 2, 38, 8, 26, 32]
  | _, _ => id6

@[expose] def n0 : Eps → ℕ
  | .plus => 12
  | .minus => 4

@[expose] def wordAct (ε : Eps) : List ℕ → ℕ → ℕ
  | [], x => x
  | i :: w, x => bmulVec 6 6 (genRows ε i) (wordAct ε w x)

@[expose] def genCheck (ε : Eps) : Bool :=
  (List.range 6).all fun i =>
    bIsId 6 (bmul 6 6 (genRows ε i) (genInvRows ε i)) &&
      bIsId 6 (bmul 6 6 (genInvRows ε i) (genRows ε i)) &&
      (List.range 64).all fun x => qfB ε (bmulVec 6 6 (genRows ε i) x) == qfB ε x

@[expose] def orbitWords : Eps → Array (List ℕ)
  | .plus =>
    #[[], [], [0, 3, 2], [0, 5, 4], [4, 2], [5, 3], [1, 4, 3], [1, 5, 2], [5, 2], [4, 3],
      [1, 5, 3], [1, 4, 2], [], [3, 2, 5, 4], [0, 5, 4], [5, 1, 0, 4], [1, 5, 4], [1, 3, 2],
      [5, 4], [1, 0, 5, 4], [0, 5, 2], [0, 4, 3], [3, 0, 4], [2, 0, 5], [0, 4, 2], [0, 5, 3],
      [3, 0, 5], [2, 0, 4], [5, 0, 0, 4], [1, 5, 4], [3, 2], [5, 4], [1, 0, 2], [2, 1, 5, 4],
      [3], [5, 3, 0, 4], [0, 0, 4], [0, 0, 5], [0, 5], [0, 4], [0, 0, 5], [0, 0, 4], [0, 4],
      [0, 5], [3, 1, 5, 4], [1, 0, 3], [5, 2, 0, 4], [2], [0, 3], [3, 5, 4], [2, 0, 5, 4],
      [0, 0, 2], [5], [4], [1, 0, 5], [1, 0, 4], [4], [5], [1, 0, 4], [1, 0, 5], [2, 5, 4],
      [0, 2], [0, 0, 3], [3, 0, 5, 4]]
  | .minus =>
    #[[], [], [4, 3, 2, 1, 0, 2, 3, 4, 1, 2, 3, 0, 2], [2, 3, 0, 2], [], [1, 2, 0, 1, 2],
      [2, 3, 0, 2], [1, 2, 3, 1, 2], [3, 1, 0, 2], [1, 3, 2], [1, 1, 2], [1, 0, 2], [3, 1, 2],
      [1, 3, 0, 2], [0, 1, 2], [1, 2], [2, 1, 0, 2, 3, 4, 1, 2, 3, 0, 2], [3, 4, 2, 3, 0, 2],
      [4, 2, 3, 0, 2], [4, 1, 2, 3, 1, 2], [3, 4, 2, 3, 0, 2], [3, 4, 1, 2, 3, 1, 2],
      [3, 2, 1, 0, 2, 3, 4, 1, 2, 3, 0, 2], [4, 2, 3, 0, 2], [4, 1, 3, 2], [4, 3, 1, 0, 2],
      [2, 3, 1, 4, 2, 3, 0, 2], [0, 2, 3, 1, 4, 2, 3, 0, 2], [4, 1, 3, 0, 2], [4, 3, 1, 2],
      [0, 2, 3, 4, 1, 2, 3, 0, 2], [2, 3, 4, 1, 2, 3, 0, 2], [1], [2, 0, 1, 2], [1, 2, 3, 0, 2],
      [2, 3, 1, 2], [2, 1, 0, 2], [0, 1], [2, 1, 3, 2], [0, 1, 2, 3, 0, 2], [3, 2], [3, 0, 2],
      [0, 2], [2], [3, 0, 2], [3, 2], [2], [0, 2], [3, 4, 1, 2, 3, 0, 2], [3, 4, 2, 3, 1, 2],
      [4, 2, 3, 1, 2], [4, 1, 2, 3, 0, 2], [3, 4, 2, 1, 3, 2], [3, 1, 4, 2, 3, 0, 2],
      [1, 4, 2, 3, 0, 2], [4, 2, 1, 3, 2], [4, 3, 0, 2], [4, 3, 2],
      [1, 0, 2, 3, 4, 1, 2, 3, 0, 2], [0, 2, 3, 4, 1, 2, 3, 1, 2], [4, 3, 2], [4, 3, 0, 2],
      [1, 2, 3, 1, 4, 2, 3, 0, 2], [2, 3, 4, 1, 2, 3, 1, 2]]

@[expose] def orbitCheck (ε : Eps) : Bool :=
  (List.range 64).all fun x =>
    x == 0 || wordAct ε ((orbitWords ε).getD x []) (if qfB ε x then n0 ε else 1) == x

@[expose] def extendCols (ε : Eps) (cs : List ℕ) : List ℕ :=
  (List.range 64).filter fun c => qfB ε c == qfB ε (2 ^ cs.length) &&
    (List.range cs.length).all fun i => bfB ε (cs.getD i 0) c == bfB ε (2 ^ i) (2 ^ cs.length)

@[expose] def oColsAux (ε : Eps) : ℕ → List ℕ → List (List ℕ)
  | 0, cs => [cs]
  | m + 1, cs => (extendCols ε cs).flatMap fun c => oColsAux ε m (cs ++ [c])

@[expose] def oCols (ε : Eps) : List (List ℕ) := oColsAux ε 6 []

@[expose] def oBound : Eps → ℕ
  | .plus => 40320
  | .minus => 51840

@[expose] def oCheck (ε : Eps) : Bool := (oCols ε).length == oBound ε

@[expose] def rankParAux : List ℕ → List ℕ → Bool → Bool
  | _, [], b => b
  | span, v :: vs, b =>
    if span.contains v then rankParAux span vs b
    else rankParAux (span ++ span.map (· ^^^ v)) vs (!b)

@[expose] def dickC (C : List ℕ) : Bool :=
  rankParAux [0] ((List.range 6).map fun j => C.getD j 0 ^^^ 2 ^ j) false

@[expose] def dickCheck (ε : Eps) : Bool :=
  (oCols ε).all fun C => dickC C ||
    (List.range 6).all fun i => !dickC (C.map (bmulVec 6 6 (genRows ε i))) &&
      !dickC (C.map (bmulVec 6 6 (genInvRows ε i)))

@[expose] def affB (d : Array ℕ × ℕ) (x : ℕ) : ℕ := bmulVec 6 6 d.1 x ^^^ d.2

@[expose] def coneX : Eps → Array ℕ × ℕ
  | .plus => (#[19, 42, 30, 60, 38, 32], 9)
  | .minus => (#[5, 3, 57, 7, 42, 49], 53)

@[expose] def coneXi : Eps → Array ℕ × ℕ
  | .plus => (#[23, 44, 28, 14, 58, 32], 31)
  | .minus => (#[11, 9, 10, 36, 22, 61], 3)

@[expose] def coneY : Eps → Array ℕ × ℕ
  | .plus => (#[42, 27, 45, 57, 30, 63], 42)
  | .minus => (#[48, 24, 56, 47, 19, 38], 58)

@[expose] def coneYi : Eps → Array ℕ × ℕ
  | .plus => (#[45, 23, 63, 11, 51, 29], 38)
  | .minus => (#[45, 58, 28, 5, 7, 6], 48)

@[expose] def coneC : Eps → List ℕ
  | .plus => [16, 9, 61, 8, 56, 3]
  | .minus => [62, 23, 38, 35, 17, 58]

@[expose] def coneComm (ε : Eps) (v : ℕ) : ℕ :=
  affB (coneX ε) (affB (coneY ε) (affB (coneXi ε) (affB (coneYi ε) v)))

@[expose] def coneCheck (ε : Eps) : Bool :=
  ((List.range 64).all fun v =>
    qfB ε (affB (coneX ε) v) == qfB ε v && qfB ε (affB (coneY ε) v) == qfB ε v &&
      affB (coneXi ε) (affB (coneX ε) v) == v && affB (coneX ε) (affB (coneXi ε) v) == v &&
      affB (coneYi ε) (affB (coneY ε) v) == v && affB (coneY ε) (affB (coneYi ε) v) == v) &&
    ((List.range 6).all fun j => coneComm ε (2 ^ j) == (coneC ε).getD j 0) &&
    coneComm ε 0 == 0 && dickC (coneC ε)

end CFSG.EvenSmallLie.OmegaEight.Stage1
