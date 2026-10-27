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

namespace CFSG.CGT.A8S.L2

@[expose] def evalD {H : Type*} [Group H] (x y : H) : List (Fin 2) → H
  | [] => 1
  | l :: w => (if l = 0 then x else y) * evalD x y w

theorem map_evalD {H K : Type*} [Group H] [Group K] (Φ : H →* K) (x y : H) (w : List (Fin 2)) :
    Φ (evalD x y w) = evalD (Φ x) (Φ y) w := by
  induction w with
  | nil => exact map_one Φ
  | cons l w ih =>
    simp only [evalD]
    rw [map_mul, ih]
    split <;> rfl

theorem evalD_mem {H : Type*} [Group H] {K : Subgroup H} {x y : H} (hx : x ∈ K) (hy : y ∈ K)
    (w : List (Fin 2)) : evalD x y w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    simp only [evalD]
    refine K.mul_mem ?_ ih
    split
    · exact hx
    · exact hy

theorem evalD_of_mulOn {H : Type*} [Group H] {K : Subgroup H} {f : H → H}
    (hf : ∀ a ∈ K, ∀ b ∈ K, f (a * b) = f a * f b) (h1 : f 1 = 1) {x y : H} (hx : x ∈ K)
    (hy : y ∈ K) (w : List (Fin 2)) : f (evalD x y w) = evalD (f x) (f y) w := by
  induction w with
  | nil => exact h1
  | cons l w ih =>
    simp only [evalD]
    rw [hf _ (by split; exacts [hx, hy]) _ (evalD_mem hx hy w), ih]
    split <;> rfl

end CFSG.CGT.A8S.L2
