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
public import Mathlib.GroupTheory.IsSubnormal
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

namespace CFSG.ComponentClassification.HarrisLit.T1.RowAlt

open Subgroup
open scoped commutatorElement

section Generic

variable {X : Type*} [Group X]

theorem exists_iterate_commutatorElement_mem {H : Subgroup X} (hH : H.IsSubnormal) {y : X}
    (hy : y ∈ H) : ∃ r : ℕ, ∀ n : X, (fun w => ⁅w, y⁆)^[r] n ∈ H := by
  induction hH generalizing y with
  | top => exact ⟨0, fun n => mem_top n⟩
  | step H K hHK _ hHn ih =>
    obtain ⟨r, hr⟩ := ih (hHK hy)
    refine ⟨r + 1, fun n => ?_⟩
    rw [Function.iterate_succ_apply']
    have hmK := hr n
    set m := (fun w => ⁅w, y⁆)^[r] n
    have hconj : m * y * m⁻¹ ∈ H := by
      have h1 : (⟨y, hHK hy⟩ : K) ∈ H.subgroupOf K := hy
      exact hHn.conj_mem _ h1 ⟨m, hmK⟩
    rw [commutatorElement_def]
    exact mul_mem hconj (inv_mem hy)

theorem iterate_commutatorElement_mem_of_normal {N : Subgroup X} (hN : N.Normal) (y : X) {n : X}
    (hn : n ∈ N) (r : ℕ) : (fun w => ⁅w, y⁆)^[r] n ∈ N := by
  induction r with
  | zero => exact hn
  | succ r ih =>
    rw [Function.iterate_succ_apply', commutatorElement_def]
    have h1 : y * ((fun w => ⁅w, y⁆)^[r] n)⁻¹ * y⁻¹ ∈ N := hN.conj_mem _ (inv_mem ih) y
    simpa [mul_assoc] using mul_mem ih h1

theorem commute_of_iterate_commutatorElement_eq_one {N : Subgroup X} {x : X}
    (hNx : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hsq : ∀ n ∈ N, n * n = 1) (hodd : Odd (orderOf x))
    {r : ℕ} (hr : ∀ n ∈ N, (fun w => ⁅w, x⁆)^[r] n = 1) : ∀ n ∈ N, x * n * x⁻¹ = n := by
  set f := fun w : X => ⁅w, x⁆ with hf
  have hfN : ∀ w ∈ N, f w ∈ N := fun w hw => by
    have h1 : x * w⁻¹ * x⁻¹ ∈ N := hNx _ (inv_mem hw)
    show w * x * w⁻¹ * x⁻¹ ∈ N
    simpa [mul_assoc] using mul_mem hw h1
  have hiter : ∀ k, ∀ w ∈ N, f^[k] w ∈ N := by
    intro k
    induction k with
    | zero => exact fun w hw => hw
    | succ k ih => exact fun w hw => by rw [Function.iterate_succ_apply']; exact hfN _ (ih w hw)
  obtain ⟨k, hk⟩ := hodd
  have hxpow : x = (x * x) ^ (k + 1) := by
    rw [← sq, ← pow_mul]
    calc x = x ^ orderOf x * x := by rw [pow_orderOf_eq_one, one_mul]
      _ = x ^ (2 * (k + 1)) := by rw [hk, ← pow_succ]; ring_nf
  have key : ∀ m ∈ N, f (f m) = 1 → f m = 1 := by
    intro m hm hffm
    have hvN : f m ∈ N := hfN m hm
    have hv2 := hsq _ hvN
    have hvinv : (f m)⁻¹ = f m := inv_eq_of_mul_eq_one_right hv2
    have hvx : x * f m * x⁻¹ = f m := by
      have h1 : f m * x * (f m)⁻¹ * x⁻¹ = 1 := hffm
      calc x * f m * x⁻¹ = (f m * x * (f m)⁻¹ * x⁻¹)⁻¹ * f m := by group
        _ = f m := by rw [h1, inv_one, one_mul]
    have hxm : x * m * x⁻¹ = (f m)⁻¹ * m := by
      show x * m * x⁻¹ = (m * x * m⁻¹ * x⁻¹)⁻¹ * m
      group
    have hx2 : x * x * m * (x * x)⁻¹ = m := by
      calc x * x * m * (x * x)⁻¹ = x * (x * m * x⁻¹) * x⁻¹ := by group
        _ = x * ((f m)⁻¹ * m) * x⁻¹ := by rw [hxm]
        _ = (x * (f m)⁻¹ * x⁻¹) * (x * m * x⁻¹) := by group
        _ = (x * f m * x⁻¹) * (x * m * x⁻¹) := by rw [hvinv]
        _ = f m * ((f m)⁻¹ * m) := by rw [hvx, hxm]
        _ = m := mul_inv_cancel_left _ _
    have hpow : ∀ j : ℕ, (x * x) ^ j * m * ((x * x) ^ j)⁻¹ = m := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc (x * x) ^ (j + 1) * m * ((x * x) ^ (j + 1))⁻¹
            = (x * x) ^ j * (x * x * m * (x * x)⁻¹) * ((x * x) ^ j)⁻¹ := by
              rw [pow_succ, mul_inv_rev]; simp only [mul_assoc]
          _ = m := by rw [hx2, ih]
    have hcm : x * m * x⁻¹ = m := by
      have h := hpow (k + 1)
      rwa [← hxpow] at h
    show m * x * m⁻¹ * x⁻¹ = 1
    calc m * x * m⁻¹ * x⁻¹ = m * (x * m * x⁻¹)⁻¹ := by group
      _ = 1 := by rw [hcm, mul_inv_cancel]
  have hdesc : ∀ j, (∀ n ∈ N, f^[j + 1] n = 1) → ∀ n ∈ N, f n = 1 := by
    intro j
    induction j with
    | zero => intro h n hn; simpa using h n hn
    | succ j ih =>
      intro h
      apply ih
      intro n hn
      have h1 := h n hn
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h1
      rw [Function.iterate_succ_apply']
      exact key _ (hiter j n hn) h1
  intro n hn
  have hf1 : f n = 1 := by
    rcases r with _ | j
    · have h0 : n = 1 := hr n hn
      subst h0
      show 1 * x * 1⁻¹ * x⁻¹ = 1
      group
    · exact hdesc j hr n hn
  have h1 : n * x * n⁻¹ * x⁻¹ = 1 := hf1
  calc x * n * x⁻¹ = (n * x * n⁻¹ * x⁻¹)⁻¹ * n := by group
    _ = n := by rw [h1, inv_one, one_mul]

end Generic

end CFSG.ComponentClassification.HarrisLit.T1.RowAlt
