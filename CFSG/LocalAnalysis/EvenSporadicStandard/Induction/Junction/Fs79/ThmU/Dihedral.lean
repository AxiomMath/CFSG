module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Basic

public section

namespace CFSG.EvenSporadicStandard.Induction.ThmU

open Subgroup CFSG.EvenSporadicStandard.Induction
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_commuting_good_bad [Finite G] {A : Subgroup G} {t₀ b : G} (ht : GoodInv A t₀)
    (hb : BadInv A b) :
    ∃ t a : G, GoodInv A t ∧ BadInv A a ∧ t * a = a * t := by
  have ht2 : t₀ * t₀ = 1 := mul_self_eq_one_of_orderOf ht.1
  have hb2 : b * b = 1 := mul_self_eq_one_of_orderOf hb.1
  have ht_inv : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right ht2
  have hb_inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hAt : ∀ a ∈ A, t₀ * a = a * t₀ :=
    fun a ha => (Subgroup.mem_centralizer_singleton_iff.1 (ht.le_centralizer ha)).symm
  have hAb : ∀ a ∈ A, b * a = a * b :=
    fun a ha => (Subgroup.mem_centralizer_singleton_iff.1 (hb.2.1 ha)).symm
  let ρ := t₀ * b
  have hρinv : ρ⁻¹ = b * t₀ := by
    show (t₀ * b)⁻¹ = b * t₀
    rw [mul_inv_rev, ht_inv, hb_inv]
  have hρA : ∀ a ∈ A, ρ * a = a * ρ := by
    intro a ha
    show (t₀ * b) * a = a * (t₀ * b)
    calc (t₀ * b) * a = t₀ * (b * a) := by group
      _ = t₀ * (a * b) := by rw [hAb a ha]
      _ = (t₀ * a) * b := by group
      _ = (a * t₀) * b := by rw [hAt a ha]
      _ = a * (t₀ * b) := by group
  have ht_conj_ρ : t₀ * ρ * t₀ = ρ⁻¹ := by
    rw [hρinv]
    show t₀ * (t₀ * b) * t₀ = b * t₀
    calc t₀ * (t₀ * b) * t₀ = (t₀ * t₀) * (b * t₀) := by group
      _ = b * t₀ := by rw [ht2, one_mul]
  have hb_conj_ρ : b * ρ * b = ρ⁻¹ := by
    rw [hρinv]
    show b * (t₀ * b) * b = b * t₀
    calc b * (t₀ * b) * b = (b * t₀) * (b * b) := by group
      _ = b * t₀ := by rw [hb2, mul_one]
  have ht_conj_zpow : ∀ j : ℤ, t₀ * ρ ^ j * t₀ = ρ ^ (-j) := by
    intro j
    have h1 : (MulAut.conj t₀) ρ = ρ⁻¹ := by
      rw [MulAut.conj_apply, ht_inv]
      exact ht_conj_ρ
    calc t₀ * ρ ^ j * t₀ = (MulAut.conj t₀) (ρ ^ j) := by
          rw [MulAut.conj_apply, ht_inv]
      _ = ((MulAut.conj t₀) ρ) ^ j := map_zpow _ _ _
      _ = (ρ⁻¹) ^ j := by rw [h1]
      _ = ρ ^ (-j) := by rw [inv_zpow']
  have hb_conj_zpow : ∀ j : ℤ, b * ρ ^ j * b = ρ ^ (-j) := by
    intro j
    have h1 : (MulAut.conj b) ρ = ρ⁻¹ := by
      rw [MulAut.conj_apply, hb_inv]
      exact hb_conj_ρ
    calc b * ρ ^ j * b = (MulAut.conj b) (ρ ^ j) := by
          rw [MulAut.conj_apply, hb_inv]
      _ = ((MulAut.conj b) ρ) ^ j := map_zpow _ _ _
      _ = (ρ⁻¹) ^ j := by rw [h1]
      _ = ρ ^ (-j) := by rw [inv_zpow']
  rcases Nat.even_or_odd (orderOf ρ) with heven | hodd
  · obtain ⟨m, hm⟩ := heven
    have hmpos : 0 < m := by have := orderOf_pos ρ; omega
    have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hmpos
    have hz_order : orderOf (ρ ^ m) = 2 := by
      have hdvd : m ∣ orderOf ρ := ⟨2, by rw [hm, mul_two]⟩
      rw [orderOf_pow_of_dvd hm0 hdvd, hm, ← two_mul m]
      exact Nat.mul_div_cancel 2 hmpos
    have hz2 : ρ ^ m * ρ ^ m = 1 := mul_self_eq_one_of_orderOf hz_order
    have hz_inv : (ρ ^ m)⁻¹ = ρ ^ m := inv_eq_of_mul_eq_one_right hz2
    have hzA_comm : ∀ a ∈ A, ρ ^ m * a = a * ρ ^ m :=
      fun a ha => Commute.pow_left (hρA a ha) m
    have hzA : A ≤ centralizer ({ρ ^ m} : Set G) := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.2 (hzA_comm a ha).symm
    have ht_conj_z : t₀ * ρ ^ m * t₀ = ρ ^ m := by
      have h := ht_conj_zpow (m : ℤ)
      have hzm : ρ ^ (-(m : ℤ)) = ρ ^ m := by rw [zpow_neg, zpow_natCast, hz_inv]
      rwa [zpow_natCast, hzm] at h
    have htz_comm : t₀ * ρ ^ m = ρ ^ m * t₀ := by
      have h := congrArg (· * t₀) ht_conj_z
      rw [mul_assoc, ht2, mul_one] at h
      exact h
    have hb_conj_z : b * ρ ^ m * b = ρ ^ m := by
      have h := hb_conj_zpow (m : ℤ)
      have hzm : ρ ^ (-(m : ℤ)) = ρ ^ m := by rw [zpow_neg, zpow_natCast, hz_inv]
      rwa [zpow_natCast, hzm] at h
    have hbz_comm : b * ρ ^ m = ρ ^ m * b := by
      have h := congrArg (· * b) hb_conj_z
      rw [mul_assoc, hb2, mul_one] at h
      exact h
    by_cases hbad : BadInv A (ρ ^ m)
    · exact ⟨t₀, ρ ^ m, ht, hbad, htz_comm⟩
    · exact ⟨ρ ^ m, b, goodInv_of_not_badInv hz_order hzA hbad, hb, hbz_comm.symm⟩
  · obtain ⟨k, hk⟩ := hodd
    have hk2 : 2 * k = orderOf ρ - 1 := by omega
    have ht_conj_pow' : t₀ * ρ ^ (-(k : ℤ)) * t₀ = ρ ^ k := by
      have h := ht_conj_zpow (-(k : ℤ))
      rwa [neg_neg, zpow_natCast] at h
    have hkey : t₀ * ρ ^ (-(k : ℤ)) = ρ ^ k * t₀ := by
      have h := congrArg (· * t₀) ht_conj_pow'
      rw [mul_assoc, ht2, mul_one] at h
      exact h
    have hcA : ∀ a ∈ A, ρ ^ k * a = a * ρ ^ k :=
      fun a ha => Commute.pow_left (hρA a ha) k
    have hc_inv : (ρ ^ k)⁻¹ = ρ ^ (-(k : ℤ)) := by rw [zpow_neg, zpow_natCast]
    have hc_conj : ρ ^ k * t₀ * (ρ ^ k)⁻¹ = b := by
      have h1 : ρ ^ k * t₀ * (ρ ^ k)⁻¹ = ρ ^ (2 * k) * t₀ := by
        calc ρ ^ k * t₀ * (ρ ^ k)⁻¹ = ρ ^ k * t₀ * ρ ^ (-(k : ℤ)) := by rw [hc_inv]
          _ = ρ ^ k * (t₀ * ρ ^ (-(k : ℤ))) := by group
          _ = ρ ^ k * (ρ ^ k * t₀) := by rw [hkey]
          _ = ρ ^ (2 * k) * t₀ := by rw [← mul_assoc, ← pow_add, two_mul]
      have h2 : ρ ^ (2 * k) = ρ⁻¹ := by
        rw [hk2]
        exact eq_inv_of_mul_eq_one_left (by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt (orderOf_pos ρ)),
            pow_orderOf_eq_one])
      rw [h1, h2, hρinv]
      rw [mul_assoc, ht2, mul_one]
    have hg : GoodInv A b := by
      have h := GoodInv.conj ht hcA
      rwa [hc_conj] at h
    exact (hb.not_goodInv hg).elim

end CFSG.EvenSporadicStandard.Induction.ThmU
