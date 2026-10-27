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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {G : Type*} [Group G]

section Inverting

variable {a r : G} (hinv : a * r = r⁻¹ * a)
include hinv

theorem mul_pow_eq_inv_pow_mul_of_inv (i : ℕ) : a * r ^ i = (r ^ i)⁻¹ * a := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, hinv, ← mul_assoc, ← mul_inv_rev,
      (Commute.self_pow r i).eq]

theorem pow_inv_mul_mul_pow_of_inv (i : ℕ) : (r ^ i)⁻¹ * a * r ^ i = (r ^ (2 * i))⁻¹ * a := by
  rw [mul_assoc, mul_pow_eq_inv_pow_mul_of_inv hinv, ← mul_assoc, ← mul_inv_rev, ← pow_add,
    two_mul]

end Inverting

theorem mul_mul_eq_inv_mul_of_involutions {a c : G} (ha : a * a = 1) (hc : c * c = 1) :
    a * (a * c) = (a * c)⁻¹ * a := by
  rw [← mul_assoc, ha, one_mul, mul_inv_rev, inv_mul_cancel_right,
    inv_eq_of_mul_eq_one_right hc]

theorem exists_conj_eq_of_odd {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hodd : Odd (orderOf (x * y))) : ∃ n : ℕ, ((x * y) ^ n)⁻¹ * x * (x * y) ^ n = y := by
  obtain ⟨s, hs⟩ := hodd
  have hinv := mul_mul_eq_inv_mul_of_involutions hx hy
  refine ⟨s + 1, ?_⟩
  rw [pow_inv_mul_mul_pow_of_inv hinv, show 2 * (s + 1) = orderOf (x * y) + 1 by omega,
    pow_succ, pow_orderOf_eq_one, one_mul, ← hinv, ← mul_assoc, hx, one_mul]

variable {H : Subgroup G} {D : Set G}

end CFSG.LocalAnalysis.ComponentInitial
