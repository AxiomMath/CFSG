module

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

@[expose] def gfAdd (a b : Nat) : Nat := (a % 7 + b % 7) % 7 + 7 * ((a / 7 + b / 7) % 7)

@[expose] def gfMul (a b : Nat) : Nat :=
  (a % 7 * (b % 7) + 6 * (a / 7 * (b / 7))) % 7 + 7 * ((a % 7 * (b / 7) + a / 7 * (b % 7)) % 7)

@[expose] def gfNeg (a : Nat) : Nat := (7 - a % 7) % 7 + 7 * ((7 - a / 7 % 7) % 7)

@[expose] def gfConj (a : Nat) : Nat := a % 7 + 7 * ((7 - a / 7 % 7) % 7)

@[expose] def gfKappa : Nat := 5

structure N7 where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  x3 : Nat
  x4 : Nat
  x5 : Nat
  x6 : Nat

@[expose] def e0N : N7 := ⟨1, 0, 0, 0, 0, 0, 0⟩

@[expose] def bfN (x y : N7) : Nat :=
  gfAdd (gfAdd (gfAdd (gfAdd (gfMul x.x0 y.x3) (gfMul y.x0 x.x3))
    (gfAdd (gfMul x.x1 y.x4) (gfMul y.x1 x.x4))) (gfAdd (gfMul x.x2 y.x5) (gfMul y.x2 x.x5)))
    (gfMul gfKappa (gfMul x.x6 y.x6))

@[expose] def tauN (x : N7) : N7 :=
  ⟨gfConj x.x3, gfConj x.x4, gfConj x.x5, gfConj x.x0, gfConj x.x1, gfConj x.x2, gfConj x.x6⟩

@[expose] def herN (x y : N7) : Nat := bfN x (tauN y)

@[expose] def gramNe (x y : N7) : Bool :=
  gfMul (herN x x) (herN y y) != gfMul (herN x y) (herN y x)

@[expose] def isFFN (x : N7) : Bool := bfN x x == 0 && herN x x != 0

@[expose] def colN (x y : N7) : Bool := bfN x y == 0 && gramNe x y

@[expose] def candN (c : N7) (b1 b2 b4 b5 b6 : Nat) : N7 :=
  ⟨gfNeg (gfAdd (gfAdd (gfAdd (gfMul c.x1 b4) (gfMul c.x2 b5)) (gfAdd (gfMul c.x4 b1)
    (gfMul c.x5 b2))) (gfMul gfKappa (gfMul c.x6 b6))), b1, b2, 0, b4, b5, b6⟩

@[expose] def candsA (c : N7) : List N7 :=
  (List.range 49).flatMap fun x2 => (List.range 49).flatMap fun x5 => (List.range 49).map fun x6 =>
    candN c 1 x2 (gfAdd (gfNeg (gfMul x2 x5)) (gfMul x6 x6)) x5 x6

@[expose] def candsB (c : N7) : List N7 :=
  (List.range 49).flatMap fun x4 => (List.range 49).map fun x6 => candN c 0 1 x4 (gfMul x6 x6) x6

@[expose] def candsC (c : N7) : List N7 := (List.range 49).map fun x5 => candN c 0 0 1 x5 0

@[expose] def candsD (c : N7) : List N7 := [candN c 0 0 0 1 0]

@[expose] def q7Cands (c : N7) : List N7 := candsA c ++ candsB c ++ candsC c ++ candsD c

@[expose] def q7Pts (c : N7) : List N7 :=
  (q7Cands c).filter fun b => isFFN b && colN e0N b && colN c b

@[expose] def bfsAux {α : Type} (adj : α → α → Bool) : Nat → List α → List α → Bool
  | 0, _, rest => rest.isEmpty
  | fuel + 1, frontier, rest =>
    rest.isEmpty ||
      (let nr := rest.partition fun u => frontier.any fun f => adj f u
       !nr.1.isEmpty && bfsAux adj fuel nr.1 nr.2)

@[expose] def bfsOk {α : Type} (adj : α → α → Bool) : List α → Bool
  | [] => true
  | r :: rest => bfsAux adj 12 [r] rest

@[expose] def q7RepsData : Array (Array Nat) := #[
  #[1, 1, 1, 1, 34, 5, 1, 38, 2, 4],
  #[1, 2, 1, 2, 31, 11, 1, 24, 25, 38],
  #[1, 2, 0, 2, 45, 24, 1, 10, 31, 4],
  #[1, 3, 1, 3, 33, 41, 1, 2, 21, 39],
  #[1, 8, 1, 43, 47, 10, 1, 44, 36, 45],
  #[1, 9, 1, 44, 3, 45, 1, 7, 35, 31],
  #[1, 10, 1, 45, 18, 48, 1, 11, 4, 42],
  #[1, 11, 1, 46, 19, 13, 1, 16, 44, 30],
  #[1, 12, 1, 47, 27, 24, 1, 46, 8, 41],
  #[1, 16, 1, 37, 45, 34, 1, 3, 23, 5],
  #[1, 17, 1, 38, 18, 7, 1, 4, 37, 40],
  #[1, 18, 1, 39, 5, 21, 1, 7, 35, 44],
  #[1, 24, 1, 31, 15, 38, 1, 2, 48, 0],
  #[1, 24, 0, 31, 0, 41, 1, 0, 12, 0],
  #[2, 0, 1, 0, 19, 3, 1, 35, 22, 37],
  #[2, 1, 1, 1, 28, 46, 1, 13, 21, 40],
  #[2, 2, 1, 2, 6, 21, 1, 4, 47, 45],
  #[2, 2, 0, 2, 47, 30, 1, 44, 33, 28],
  #[2, 3, 1, 3, 22, 46, 1, 17, 44, 43],
  #[2, 3, 0, 3, 34, 3, 1, 29, 4, 28],
  #[2, 8, 1, 43, 22, 34, 1, 24, 13, 34],
  #[2, 8, 0, 43, 2, 38, 1, 25, 38, 0],
  #[2, 9, 1, 44, 18, 26, 1, 23, 32, 39],
  #[2, 10, 1, 45, 26, 34, 1, 32, 30, 0],
  #[2, 11, 1, 46, 22, 14, 1, 15, 20, 30],
  #[2, 12, 1, 47, 13, 2, 1, 20, 44, 45],
  #[2, 16, 1, 37, 2, 3, 1, 39, 27, 31],
  #[2, 17, 1, 38, 30, 27, 1, 32, 24, 5],
  #[2, 18, 1, 39, 17, 19, 1, 3, 14, 4],
  #[2, 24, 1, 31, 15, 36, 1, 24, 12, 32],
  #[2, 24, 0, 31, 32, 36, 1, 35, 20, 0],
  #[3, 0, 1, 0, 30, 41, 1, 33, 46, 4],
  #[3, 1, 1, 1, 29, 6, 1, 2, 47, 38],
  #[3, 2, 1, 2, 16, 2, 1, 30, 43, 31],
  #[3, 3, 1, 3, 11, 24, 1, 40, 8, 36],
  #[3, 8, 1, 43, 12, 20, 1, 40, 42, 30],
  #[3, 9, 1, 44, 39, 10, 1, 38, 7, 30],
  #[3, 10, 1, 45, 42, 37, 1, 38, 21, 48],
  #[3, 11, 1, 46, 24, 48, 1, 46, 45, 46],
  #[3, 12, 1, 47, 10, 22, 1, 19, 42, 48],
  #[3, 16, 1, 37, 9, 3, 1, 24, 6, 4],
  #[3, 17, 1, 38, 4, 17, 1, 23, 33, 41],
  #[3, 18, 1, 39, 4, 6, 1, 10, 17, 42],
  #[3, 24, 1, 31, 15, 12, 1, 41, 26, 37],
  #[4, 0, 1, 0, 28, 36, 1, 48, 23, 38],
  #[4, 1, 1, 1, 38, 3, 1, 5, 12, 35],
  #[4, 1, 0, 1, 25, 44, 1, 24, 47, 42],
  #[4, 2, 1, 2, 36, 31, 1, 13, 33, 4],
  #[4, 3, 1, 3, 21, 30, 1, 4, 25, 34],
  #[4, 3, 0, 3, 2, 8, 1, 2, 43, 4],
  #[4, 8, 1, 43, 43, 46, 1, 7, 25, 40],
  #[4, 8, 0, 43, 12, 3, 1, 41, 43, 46],
  #[4, 9, 1, 44, 38, 27, 1, 36, 32, 34],
  #[4, 10, 1, 45, 34, 42, 1, 23, 48, 33],
  #[4, 11, 1, 46, 10, 33, 1, 25, 5, 47],
  #[4, 12, 1, 47, 14, 19, 1, 18, 23, 39],
  #[4, 16, 1, 37, 5, 30, 1, 2, 0, 39],
  #[4, 16, 0, 37, 2, 32, 1, 31, 14, 0],
  #[4, 17, 1, 38, 40, 41, 1, 32, 3, 32],
  #[4, 18, 1, 39, 48, 35, 1, 15, 39, 45],
  #[4, 24, 1, 31, 9, 14, 1, 38, 18, 32],
  #[5, 0, 1, 0, 28, 25, 1, 26, 40, 37],
  #[5, 1, 1, 1, 42, 4, 1, 38, 43, 35],
  #[5, 2, 1, 2, 27, 37, 1, 20, 48, 48],
  #[5, 3, 1, 3, 17, 17, 1, 47, 18, 0],
  #[5, 8, 1, 43, 43, 39, 1, 10, 10, 38],
  #[5, 9, 1, 44, 21, 30, 1, 46, 7, 46],
  #[5, 10, 1, 45, 6, 27, 1, 3, 11, 31],
  #[5, 11, 1, 46, 15, 13, 1, 42, 17, 46],
  #[5, 12, 1, 47, 34, 25, 1, 23, 16, 32],
  #[5, 16, 1, 37, 11, 15, 1, 1, 10, 37],
  #[5, 17, 1, 38, 48, 1, 1, 3, 11, 36],
  #[5, 18, 1, 39, 42, 30, 1, 26, 12, 29],
  #[5, 24, 1, 31, 5, 29, 1, 34, 18, 6],
  #[6, 0, 1, 0, 10, 1, 1, 13, 39, 0],
  #[6, 1, 1, 1, 40, 30, 1, 0, 4, 30],
  #[6, 2, 1, 2, 45, 6, 1, 31, 23, 34],
  #[6, 3, 1, 3, 14, 12, 1, 3, 1, 6],
  #[6, 8, 1, 43, 20, 13, 1, 34, 33, 29],
  #[6, 9, 1, 44, 17, 11, 1, 15, 5, 43],
  #[6, 10, 1, 45, 48, 4, 1, 35, 12, 43],
  #[6, 11, 1, 46, 8, 22, 1, 10, 8, 5],
  #[6, 12, 1, 47, 28, 16, 1, 41, 5, 33],
  #[6, 16, 1, 37, 5, 42, 1, 3, 12, 5],
  #[6, 17, 1, 38, 36, 41, 1, 12, 45, 39],
  #[6, 18, 1, 39, 44, 17, 1, 6, 27, 37],
  #[6, 24, 1, 31, 27, 37, 1, 2, 18, 34],
  #[1, 0, 102, 0, 0, 0, 1, 0, 0, 0],
  #[1, 0, 131, 0, 0, 1, 1, 0, 1, 6],
  #[1, 0, 146, 0, 0, 9, 1, 0, 20, 44],
  #[1, 0, 104, 0, 0, 0, 1, 1, 17, 0]]

@[expose] def rowN (row : Array Nat) : N7 :=
  ⟨row[3]!, row[4]!, row[5]!, row[6]!, row[7]!, row[8]!, row[9]!⟩

@[expose] def q7RowCheck (row : Array Nat) : Bool :=
  (rowN row).x3 == 1 && isFFN (rowN row) && bfsOk colN (q7Pts (rowN row))

@[expose] def q7MuCheck : Bool := q7RepsData.all q7RowCheck

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
