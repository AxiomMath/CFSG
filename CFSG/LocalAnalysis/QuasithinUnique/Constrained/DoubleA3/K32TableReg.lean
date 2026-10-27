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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.QuasithinUnique.DoubleA3

open Polynomial

section Scalar

variable {F R : Type*} [Field F] [CharP F 2] [Ring R] [Algebra F R] [Nontrivial R]

omit [CharP F 2] in
theorem k32_algebraMap_eq_zero_of_nilpotent {s : F} (h : IsNilpotent (algebraMap F R s)) :
    s = 0 := by
  obtain ⟨j, hj⟩ := h
  rw [← map_pow] at hj
  have hs : s ^ j = 0 := (algebraMap F R).injective (by rw [hj, map_zero])
  exact (pow_eq_zero_iff'.mp hs).1

theorem k32_reg_scalar {x₀ c : F} {n : R} (hn : IsNilpotent n) (hc : c ≠ 0)
    (h3 : (algebraMap F R x₀ + n) ^ 3 = algebraMap F R c) : n = 0 := by
  set a : R := algebraMap F R x₀ with ha
  have hcomm : Commute a n := Algebra.commutes x₀ n
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have h2R : (2 : R) = 0 := by
    calc (2 : R) = algebraMap F R 2 := (map_ofNat _ 2).symm
      _ = 0 := by rw [h2F, map_zero]
  have hx₀ : x₀ ≠ 0 := by
    intro h0
    have hz : a = 0 := by rw [ha, h0, map_zero]
    rw [hz, zero_add] at h3
    exact hc (k32_algebraMap_eq_zero_of_nilpotent (h3 ▸ hn.pow_succ 2))
  have hg := hcomm.symm.geom_sum₂_mul_add 3
  rw [add_comm n a, h3] at hg
  set w : R := ∑ i ∈ Finset.range 3, (a + n) ^ i * a ^ (3 - 1 - i) with hw
  have hwn : w * n = algebraMap F R (c - x₀ ^ 3) := by
    rw [map_sub, map_pow, ← ha]
    exact eq_sub_of_add_eq hg
  have hcn : Commute n a := hcomm.symm
  have han : Commute (a + n) n := hcomm.add_left (Commute.refl n)
  have hwc : Commute w n := by
    refine Commute.sum_left _ _ _ fun i _ => ?_
    exact (han.pow_left i).mul_left (hcn.symm.pow_left _)
  have hnil : IsNilpotent (algebraMap F R (c - x₀ ^ 3)) := by
    rw [← hwn]
    exact hwc.isNilpotent_mul_left hn
  have hs : c - x₀ ^ 3 = 0 := k32_algebraMap_eq_zero_of_nilpotent hnil
  rw [hs, map_zero] at hwn
  have hw' : w = a ^ 2 + n * (a + n) := by
    have e : n * a = a * n := hcomm.symm.eq
    have h : w = a ^ 2 + n * (a + n) + 2 * (a ^ 2 + n * a) := by
      simp only [hw, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, pow_two,
        one_mul, zero_add]
      norm_num
      noncomm_ring
      rw [← e]
      abel
    rw [h, h2R, zero_mul, add_zero]
  have hunit : IsUnit w := by
    rw [hw']
    have hu : IsUnit (a ^ 2) := by
      rw [ha, ← map_pow]
      exact (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hx₀)).map (algebraMap F R)
    have hnil2 : IsNilpotent (n * (a + n)) :=
      (hcn.add_right (Commute.refl n)).isNilpotent_mul_right hn
    have ha2 : a ^ 2 = algebraMap F R (x₀ ^ 2) := by rw [ha, map_pow]
    have hcu : Commute (a ^ 2) (n * (a + n)) := by
      rw [ha2]
      exact Algebra.commutes _ _
    exact hnil2.isUnit_add_left_of_commute hu hcu.symm
  exact (hunit.mul_right_eq_zero).mp hwn

end Scalar

section Cyclic

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem k32_commute_aeval {N A : Module.End F V} (h : Commute N A) (p : F[X]) :
    Commute (aeval N p) A := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact hp.add_left hq
  | monomial k a =>
    rw [aeval_monomial]
    exact (show Commute (algebraMap F (Module.End F V) a) A from Algebra.commutes a A).mul_left
      (h.pow_left k)

theorem k32_eq_aeval_of_cyclic {N A : Module.End F V} (h : Commute N A) {v : V}
    (hv : ∀ w : V, ∃ p : F[X], w = aeval N p v) : ∃ p : F[X], A = aeval N p := by
  obtain ⟨p, hp⟩ := hv (A v)
  refine ⟨p, LinearMap.ext fun w => ?_⟩
  obtain ⟨q, rfl⟩ := hv w
  have h1 : A (aeval N q v) = aeval N q (A v) := by
    have := congrArg (fun T : Module.End F V => T v) (k32_commute_aeval h q).eq
    simpa using this.symm
  rw [h1, hp]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

theorem k32_scalar_of_commute_cyclic [CharP F 2] [Nontrivial V] {N A : Module.End F V}
    (h : Commute N A) (hN : IsNilpotent N) {v : V} (hv : ∀ w : V, ∃ p : F[X], w = aeval N p v)
    {c : F} (hc : c ≠ 0) (hA : A ^ 3 = algebraMap F (Module.End F V) c) :
    ∃ x₀ : F, A = algebraMap F (Module.End F V) x₀ := by
  obtain ⟨p, rfl⟩ := k32_eq_aeval_of_cyclic h hv
  have hp : aeval N p = aeval N (divX p) * N + algebraMap F _ (p.coeff 0) := by
    conv_lhs => rw [← divX_mul_X_add p]
    simp
  have hn : IsNilpotent (aeval N (divX p) * N) :=
    (k32_commute_aeval (Commute.refl N) _).isNilpotent_mul_left hN
  rw [hp, add_comm] at hA
  have h0 : aeval N (divX p) * N = 0 := k32_reg_scalar hn hc hA
  exact ⟨p.coeff 0, by rw [hp, h0, zero_add]⟩

end Cyclic

end CFSG.QuasithinUnique.DoubleA3
