module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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

namespace CFSG.LargeExtraspecial.S11

open Subgroup

variable {H : Type*} [Group H]

theorem eq_one_or_eq_or_eq_inv_of_orderOf_eq_three {y x : H} (hy : orderOf y = 3)
    (hx : x ∈ zpowers y) : x = 1 ∨ x = y ∨ x = y⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have hmod := zpow_mod_orderOf y k
  rw [hy] at hmod
  rw [← hmod]
  have h0 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h3 : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  interval_cases h : k % ((3 : ℕ) : ℤ)
  · left; simp
  · right; left; simp
  · right; right
    rw [show (2 : ℤ) = ((3 : ℕ) : ℤ) - 1 by norm_num, zpow_sub_one, zpow_natCast, hy3, one_mul]

structure Sigma3 (t y : H) (N : Subgroup H) : Prop where
  normal : N.Normal
  mul_self : t * t = 1
  orderOf_eq : orderOf y = 3
  eq_zpowers : N = zpowers y
  inv : t * y * t⁻¹ = y⁻¹
  comm_mem : ∀ x : H, x * t * x⁻¹ * t⁻¹ ∈ N

theorem exists_inv_of_card_three [Finite H] {t : H} {N : Subgroup H} (hN : N.Normal)
    (hcard : Nat.card N = 3) (ht2 : t * t = 1) (hcomm : ∀ x : H, x * t * x⁻¹ * t⁻¹ ∈ N)
    (hnc : ¬ ∀ x : H, x * t * x⁻¹ = t) : ∃ y : H, Sigma3 t y N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNb : N ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hcard
    omega
  obtain ⟨⟨y, hyN⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hNb
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyo : orderOf y = 3 := by
    have hdvd : orderOf y ∣ 3 := hcard ▸ Subgroup.orderOf_dvd_natCard _ hyN
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1'
    · exact h
  have hNy : N = zpowers y := by
    refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hyN) ?_).symm
    rw [Nat.card_zpowers, hyo, hcard]
  have hmemN : ∀ n ∈ N, n = 1 ∨ n = y ∨ n = y⁻¹ := fun n hn =>
    eq_one_or_eq_or_eq_inv_of_orderOf_eq_three hyo (hNy ▸ hn)
  have hty : t * y * t⁻¹ ∈ N := hN.conj_mem y hyN t
  refine ⟨y, hN, ht2, hyo, hNy, ?_, hcomm⟩
  rcases hmemN _ hty with h | h | h
  · exfalso
    apply hy1'
    calc y = t⁻¹ * (t * y * t⁻¹) * t := by group
      _ = 1 := by rw [h]; group
  · exfalso
    apply hnc
    intro x
    have hc : x * t * x⁻¹ * t⁻¹ ∈ N := hcomm x
    have htn : ∀ n ∈ N, t * n = n * t := by
      intro n hn
      rw [hNy] at hn
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
      have hc' : Commute t y := by
        have : t * y = y * t := by
          calc t * y = (t * y * t⁻¹) * t := by group
            _ = y * t := by rw [h]
        exact this
      exact (hc'.zpow_right k).eq
    set n := x * t * x⁻¹ * t⁻¹ with hn
    have hxt : x * t * x⁻¹ = n * t := by rw [hn]; group
    have hsq : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
      calc (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    have hn2 : n * n = 1 := by
      have e : (n * t) * (n * t) = n * n * (t * t) := by
        calc (n * t) * (n * t) = n * (t * n) * t := by group
          _ = n * (n * t) * t := by rw [htn n hc]
          _ = n * n * (t * t) := by group
      rw [hxt, e, ht2, mul_one] at hsq
      exact hsq
    have hno : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hn2)
    have hno3 : orderOf n ∣ 3 := hcard ▸ Subgroup.orderOf_dvd_natCard _ hc
    have h1 : orderOf n = 1 := by
      have := Nat.dvd_gcd hno hno3
      rwa [show Nat.gcd 2 3 = 1 by norm_num, Nat.dvd_one] at this
    rw [hxt, orderOf_eq_one_iff.mp h1, one_mul]
  · exact h

namespace Sigma3

variable {t y : H} {N : Subgroup H} (hS : Sigma3 t y N)
include hS

theorem mem_iff {n : H} : n ∈ N → n = 1 ∨ n = y ∨ n = y⁻¹ := fun hn =>
  eq_one_or_eq_or_eq_inv_of_orderOf_eq_three hS.orderOf_eq (hS.eq_zpowers ▸ hn)

theorem y_mem : y ∈ N := hS.eq_zpowers ▸ mem_zpowers y

theorem pow_three : y ^ 3 = 1 := by rw [← hS.orderOf_eq]; exact pow_orderOf_eq_one y

theorem inv_eq : y⁻¹ = y * y := by
  have h3 := hS.pow_three
  rw [pow_succ, pow_two] at h3
  exact (eq_inv_of_mul_eq_one_left h3).symm

theorem ne_one : y ≠ 1 := by
  intro h
  have h3 := hS.orderOf_eq
  rw [h, orderOf_one] at h3
  omega

theorem mul_mul_self : y * y * y = 1 := by
  have h3 := hS.pow_three
  rwa [pow_succ, pow_two] at h3

theorem inv_mul_inv : y⁻¹ * y⁻¹ = y := by
  calc y⁻¹ * y⁻¹ = y⁻¹ * y⁻¹ * (y * y * y) := by rw [hS.mul_mul_self, mul_one]
    _ = y := by group

theorem t_mul_y : t * y = y⁻¹ * t := by
  calc t * y = (t * y * t⁻¹) * t := by group
    _ = y⁻¹ * t := by rw [hS.inv]

theorem t_mul_y_inv : t * y⁻¹ = y * t := by
  calc t * y⁻¹ = (t * y * t⁻¹)⁻¹ * t := by group
    _ = y * t := by rw [hS.inv, inv_inv]

theorem exists_mem_cent (x : H) :
    ∃ u : H, (u = 1 ∨ u = y ∨ u = y⁻¹) ∧ (u⁻¹ * x) * t = t * (u⁻¹ * x) := by
  have hc := hS.mem_iff (hS.comm_mem x)
  have key : ∀ u : H, x * t * x⁻¹ = u * t * u⁻¹ → (u⁻¹ * x) * t = t * (u⁻¹ * x) := by
    intro u hu
    calc (u⁻¹ * x) * t = u⁻¹ * (x * t * x⁻¹) * x := by group
      _ = u⁻¹ * (u * t * u⁻¹) * x := by rw [hu]
      _ = t * (u⁻¹ * x) := by group
  have hxt : x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t := by group
  rcases hc with h | h | h
  · refine ⟨1, Or.inl rfl, key 1 ?_⟩
    rw [hxt, h]
    group
  · refine ⟨y⁻¹, Or.inr (Or.inr rfl), key y⁻¹ ?_⟩
    rw [hxt, h, inv_inv, mul_assoc, hS.t_mul_y, ← mul_assoc, hS.inv_mul_inv]
  · refine ⟨y, Or.inr (Or.inl rfl), key y ?_⟩
    rw [hxt, h, mul_assoc, hS.t_mul_y_inv, ← mul_assoc, ← hS.inv_eq]

theorem commute_or_commute (c : H) :
    c * y = y * c ∨ (t * c) * y = y * (t * c) := by
  rcases hS.mem_iff (hS.normal.conj_mem y hS.y_mem c) with h | h | h
  · exfalso
    apply hS.ne_one
    calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  · left
    calc c * y = (c * y * c⁻¹) * c := by group
      _ = y * c := by rw [h]
  · right
    calc (t * c) * y = t * (c * y * c⁻¹) * c := by group
      _ = t * y⁻¹ * c := by rw [h]
      _ = y * t * c := by rw [hS.t_mul_y_inv]
      _ = y * (t * c) := by group

end Sigma3

end CFSG.LargeExtraspecial.S11
