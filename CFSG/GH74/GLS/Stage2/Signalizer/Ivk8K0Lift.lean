module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Group
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0

open Subgroup

theorem exists_odd_order_lift {X : Type*} [Group X] [Finite X] {N : Subgroup X} [N.Normal]
    (y₀ : X) (hodd : Odd (orderOf (QuotientGroup.mk y₀ : X ⧸ N))) :
    ∃ y₁ : X, (QuotientGroup.mk y₁ : X ⧸ N) = QuotientGroup.mk y₀ ∧ Odd (orderOf y₁) := by
  have hn : orderOf y₀ ≠ 0 := (orderOf_pos y₀).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have h2a : (2 ^ a : ℕ) ∣ orderOf y₀ := ⟨m, hnm⟩
  have hord2 : orderOf (y₀ ^ (2 ^ a)) = m := by
    rw [orderOf_pow_of_dvd (by positivity) h2a, hnm, Nat.mul_div_cancel_left _ (by positivity)]
  have hcop : Nat.Coprime (2 ^ a) (orderOf (QuotientGroup.mk y₀ : X ⧸ N)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(y₀ ^ (2 ^ a)) ^ t, ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, QuotientGroup.mk_pow]
    exact ht
  · have h1 : ((y₀ ^ (2 ^ a)) ^ t) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← hord2, pow_orderOf_eq_one, one_pow]
    exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)

theorem exists_fixed_lift {X : Type*} [Group X] (θ : MulAut X) (hθ : ∀ x, θ (θ x) = x)
    {y₁ w : X} (hw : θ y₁ = y₁ * w) {b : ℕ} (hb : Odd b) (hwb : w ^ b = 1) :
    ∃ n ∈ Subgroup.zpowers w, θ (y₁ * n) = y₁ * n := by
  obtain ⟨k, rfl⟩ := hb
  have hθw : θ w = w⁻¹ := by
    have h1 : θ (y₁ * w) = y₁ := by rw [← hw, hθ]
    rw [map_mul, hw] at h1
    have h2 : y₁ * (w * θ w) = y₁ := by rw [← mul_assoc]; exact h1
    exact eq_inv_of_mul_eq_one_right (mul_left_cancel (h2.trans (mul_one y₁).symm))
  refine ⟨w ^ (k + 1), Subgroup.pow_mem _ (Subgroup.mem_zpowers w) _, ?_⟩
  rw [map_mul, hw, map_pow, hθw, inv_pow]
  have h3 : w * (w ^ (k + 1))⁻¹ = w ^ (k + 1) := by
    rw [mul_inv_eq_iff_eq_mul, ← pow_add]
    have : k + 1 + (k + 1) = (2 * k + 1) + 1 := by ring
    rw [this, pow_succ, hwb, one_mul]
  rw [mul_assoc, h3]

theorem exists_fixed_lift_of_odd {X : Type*} [Group X] (θ : MulAut X) (hθ : ∀ x, θ (θ x) = x)
    {y₁ : X} (hodd : Odd (orderOf y₁)) (hc : y₁⁻¹ * θ y₁ ∈ center X) :
    ∃ y : X, θ y = y ∧ y⁻¹ * y₁ ∈ center X := by
  set w := y₁⁻¹ * θ y₁ with hwdef
  have hw : θ y₁ = y₁ * w := by rw [hwdef]; group
  have hwc : Commute y₁ w := Subgroup.mem_center_iff.mp hc y₁
  have hwb : w ^ orderOf y₁ = 1 := by
    have h1 : (θ y₁) ^ orderOf y₁ = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [hw, hwc.mul_pow, pow_orderOf_eq_one, one_mul] at h1
    exact h1
  obtain ⟨n, hn, hfix⟩ := exists_fixed_lift θ hθ hw hodd hwb
  refine ⟨y₁ * n, hfix, ?_⟩
  have hnc : n ∈ center X := (Subgroup.zpowers_le.mpr hc) hn
  have : (y₁ * n)⁻¹ * y₁ = n⁻¹ := by group
  rw [this]
  exact Subgroup.inv_mem _ hnc

theorem exists_fixed_lift_of_card_odd {X : Type*} [Group X] (θ : MulAut X)
    (hθ : ∀ x, θ (θ x) = x) (hodd : Odd (Nat.card (center X))) {y₁ : X}
    (hc : y₁⁻¹ * θ y₁ ∈ center X) : ∃ y : X, θ y = y ∧ y⁻¹ * y₁ ∈ center X := by
  set w := y₁⁻¹ * θ y₁ with hwdef
  have hw : θ y₁ = y₁ * w := by rw [hwdef]; group
  have hwb : w ^ Nat.card (center X) = 1 := by
    have : (⟨w, hc⟩ : ↥(center X)) ^ Nat.card (center X) = 1 := pow_card_eq_one'
    exact congrArg Subtype.val this
  obtain ⟨n, hn, hfix⟩ := exists_fixed_lift θ hθ hw hodd hwb
  refine ⟨y₁ * n, hfix, ?_⟩
  have hnc : n ∈ center X := (Subgroup.zpowers_le.mpr hc) hn
  have : (y₁ * n)⁻¹ * y₁ = n⁻¹ := by group
  rw [this]
  exact Subgroup.inv_mem _ hnc

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0
