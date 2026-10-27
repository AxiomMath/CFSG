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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo

open Finset

theorem comb_pattern {K : Type} [Field K] [Fintype K] [DecidableEq K] (hK : Fintype.card K = 4)
    {n : ℕ} (c : Fin n → K) (hc0 : ∀ i, c i ≠ 0) {lam : K} (hlam : lam ≠ 0)
    (h1 : ∀ ν : K, ν ≠ 0 → ν ≠ lam → (univ.filter fun i => c i = ν).card ≤ 1)
    (h3 : (univ.filter fun i => c i = lam).card ≤ 3) :
    n ≤ 5 ∧ (4 ≤ n → lam = 1 → ∏ i, c i = 1 → (univ.filter fun i => c i = 1).card = n - 2) := by
  classical
  set S0 : Finset K := univ.erase 0 with hS0
  have hS0card : S0.card = 3 := by
    rw [hS0, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, hK]
  have hfib : n = ∑ ν ∈ S0, (univ.filter fun i => c i = ν).card := by
    have := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (t := S0) (f := c)
      (fun i _ => mem_erase.2 ⟨hc0 i, mem_univ _⟩)
    simpa using this
  have hlamS : lam ∈ S0 := mem_erase.2 ⟨hlam, mem_univ _⟩
  have hsum : ∑ ν ∈ S0, (univ.filter fun i => c i = ν).card =
      (univ.filter fun i => c i = lam).card +
        ∑ ν ∈ S0.erase lam, (univ.filter fun i => c i = ν).card :=
    (Finset.add_sum_erase S0 _ hlamS).symm
  have hrest : ∑ ν ∈ S0.erase lam, (univ.filter fun i => c i = ν).card ≤ 2 := by
    have hcard : (S0.erase lam).card = 2 := by
      rw [Finset.card_erase_of_mem hlamS, hS0card]
    calc ∑ ν ∈ S0.erase lam, (univ.filter fun i => c i = ν).card
        ≤ ∑ _ν ∈ S0.erase lam, 1 := Finset.sum_le_sum fun ν hν => by
          have := mem_erase.1 hν
          have h0 := mem_erase.1 this.2
          exact h1 ν h0.1 this.1
      _ = 2 := by rw [Finset.sum_const, hcard]; simp
  refine ⟨by omega, fun hn4 hlam1 hprod => ?_⟩
  subst hlam1
  have hcard2 : (S0.erase 1).card = 2 := by
    rw [Finset.card_erase_of_mem hlamS, hS0card]
  obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.1 hcard2
  have ha : a ∈ S0.erase 1 := by rw [hS]; simp
  have hb : b ∈ S0.erase 1 := by rw [hS]; simp
  have ha1 : a ≠ 1 := (mem_erase.1 ha).1
  have hb1 : b ≠ 1 := (mem_erase.1 hb).1
  have ha0 : a ≠ 0 := (mem_erase.1 (mem_erase.1 ha).2).1
  have hb0 : b ≠ 0 := (mem_erase.1 (mem_erase.1 hb).2).1
  have hka := h1 a ha0 ha1
  have hkb := h1 b hb0 hb1
  have hsum' : n = (univ.filter fun i => c i = 1).card +
      ((univ.filter fun i => c i = a).card + (univ.filter fun i => c i = b).card) := by
    have := hfib
    rw [hsum, hS, Finset.sum_pair hab] at this
    exact this
  have hprod' : ∏ i, c i = a ^ (univ.filter fun i => c i = a).card *
      b ^ (univ.filter fun i => c i = b).card := by
    have hfp := Finset.prod_fiberwise_of_maps_to (s := (univ : Finset (Fin n))) (t := S0) (g := c)
      (fun i _ => mem_erase.2 ⟨hc0 i, mem_univ _⟩) (f := fun i => c i)
    rw [← hfp, ← Finset.mul_prod_erase S0 _ hlamS, hS, Finset.prod_pair hab]
    have e1 : ∀ i ∈ univ.filter (fun i => c i = 1), c i = 1 := fun i hi => (mem_filter.1 hi).2
    have e2 : ∀ i ∈ univ.filter (fun i => c i = a), c i = a := fun i hi => (mem_filter.1 hi).2
    have e3 : ∀ i ∈ univ.filter (fun i => c i = b), c i = b := fun i hi => (mem_filter.1 hi).2
    rw [Finset.prod_congr rfl e1, Finset.prod_congr rfl e2, Finset.prod_congr rfl e3]
    simp
  rw [hprod'] at hprod
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hka with h0 | h0 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hkb with h0' | h0'
  · rw [h0, h0'] at hsum'
    omega
  · exfalso
    rw [h0, h0'] at hprod
    exact hb1 (by simpa using hprod)
  · exfalso
    rw [h0, h0'] at hprod
    exact ha1 (by simpa using hprod)
  · rw [h0, h0'] at hsum'
    omega

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo
