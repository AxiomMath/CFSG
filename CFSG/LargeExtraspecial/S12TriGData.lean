module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LargeExtraspecial.S12Tri

open Equiv

@[expose] def a6a : Perm (Fin 6) := swap 2 3 * swap 4 5

@[expose] def a6b : Perm (Fin 6) := swap 0 2 * (swap 1 5 * swap 1 4 * swap 1 3)

@[expose] def a6Pair (x y : Perm (Fin 6)) : Bool :=
  decide (x ^ 2 = 1) && decide (x ≠ 1) && decide (y ^ 4 = 1) && decide (y ^ 2 ≠ 1) &&
    decide ((x * y) ^ 5 = 1) && decide (x * y ≠ 1) && decide (Perm.sign x = 1) &&
      decide (Perm.sign y = 1)

@[expose] def bfsStep (L : List (Perm (Fin 6))) : List (Perm (Fin 6)) :=
  (L ++ L.map (a6a * ·) ++ L.map (a6b * ·)).dedup

@[expose] def bfs : ℕ → List (Perm (Fin 6))
  | 0 => [1]
  | n + 1 => bfsStep (bfs n)

@[expose] def a6Count : ℕ :=
  ((Finset.univ : Finset (Perm (Fin 6) × Perm (Fin 6))).filter fun p => a6Pair p.1 p.2 = true).card

@[expose] def a6Check : Bool :=
  ((bfs 16).length == 360) && a6Pair a6a a6b && Nat.ble a6Count 1440

@[expose] def a5a : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def a5b : Perm (Fin 5) := swap 0 4 * swap 0 2

@[expose] def a5Pair (x y : Perm (Fin 5)) : Bool :=
  decide (x ^ 2 = 1) && decide (x ≠ 1) && decide (y ^ 3 = 1) && decide (y ≠ 1) &&
    decide ((x * y) ^ 5 = 1) && decide (x * y ≠ 1) && decide (Perm.sign x = 1) &&
      decide (Perm.sign y = 1)

@[expose] def bfs5Step (L : List (Perm (Fin 5))) : List (Perm (Fin 5)) :=
  (L ++ L.map (a5a * ·) ++ L.map (a5b * ·)).dedup

@[expose] def bfs5 : ℕ → List (Perm (Fin 5))
  | 0 => [1]
  | n + 1 => bfs5Step (bfs5 n)

@[expose] def a5Count : ℕ :=
  ((Finset.univ : Finset (Perm (Fin 5) × Perm (Fin 5))).filter fun p => a5Pair p.1 p.2 = true).card

@[expose] def a5Check : Bool :=
  ((bfs5 12).length == 60) && a5Pair a5a a5b && Nat.ble a5Count 120

end CFSG.LargeExtraspecial.S12Tri
