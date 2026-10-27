module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYGrp
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open Subgroup Equiv
open scoped commutatorElement

section Aux

variable {Q : Type*} [Group Q]

theorem mem_of_odd_order_of_index_two {Q₁ : Subgroup Q} (hQ₁ : Q₁.index = 2) {x : Q}
    (hx : Odd (orderOf x)) : x ∈ Q₁ := by
  have hn : Q₁.Normal := Subgroup.normal_of_index_eq_two hQ₁
  have h2 := Subgroup.pow_index_mem Q₁ x
  rw [hQ₁] at h2
  obtain ⟨k, hk⟩ := hx
  have hpow : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have : x = (x ^ 2) ^ (k + 1) := by
    rw [← pow_mul]
    calc x = x ^ (2 * k + 1) * x := by rw [hpow, one_mul]
      _ = x ^ (2 * (k + 1)) := by rw [← pow_succ]; congr 1
  rw [this]
  exact Q₁.pow_mem h2 _

end Aux

section Main

variable {Q : Type*} [Group Q] [Finite Q]

theorem mem_commutator_of_index_two (hQ : Nat.card Q = 1200) (f : Perm (Fin 5) →* Q)
    (hf : Function.Injective f) {t r : Q} (ht : t ∈ center Q) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hr : r ∈ center Q) (hr5 : orderOf r = 5) {Q₁ QL : Subgroup Q} (hQ₁ : Q₁.index = 2)
    (htQ₁ : t ∈ Q₁) (hrQ₁ : r ∈ Q₁) (hQL : QL ≤ Q₁) (htL : t ∉ QL)
    (hcomm : ∀ x ∈ Q₁, ∀ y ∈ Q₁, ⁅x, y⁆ ∈ QL) {u : Q} (huL : u ∈ QL) (hu2 : u * u = 1) :
    u ∈ commutator Q := by
  set A : Subgroup Q := (alternatingGroup (Fin 5)).map f with hA
  have h5 : 5 ≤ Nat.card (Fin 5) := by simp
  have hAperf : ⁅A, A⁆ = A := by
    rw [hA, ← Subgroup.map_commutator, commutator_alternatingGroup_eq_self h5]
  have hAQ₁ : A ≤ Q₁ := by
    rw [hA, Subgroup.map_le_iff_le_comap, ← Equiv.Perm.closure_three_cycles_eq_alternating
      (α := Fin 5), Subgroup.closure_le]
    intro σ hσ
    have h3 : orderOf (f σ) = 3 := by
      rw [orderOf_injective f hf σ, hσ.orderOf]
    exact mem_of_odd_order_of_index_two hQ₁ (by rw [h3]; decide)
  have hAQL : A ≤ QL := by
    rw [← hAperf, Subgroup.commutator_le]
    intro a ha b hb
    exact hcomm a (hAQ₁ ha) b (hAQ₁ hb)
  set Z : Subgroup Q := zpowers t ⊔ zpowers r with hZ
  have hZc : ∀ z ∈ Z, ∀ q : Q, z * q = q * z := by
    intro z hz q
    have hcen : Z ≤ center Q := sup_le (zpowers_le.2 ht) (zpowers_le.2 hr)
    exact (mem_center_iff.1 (hcen hz) q).symm
  have htr : ∀ a ∈ zpowers t, ∀ b ∈ zpowers r, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (show Commute t r from (mem_center_iff.1 hr t)) m n).eq
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hZd : zpowers t ⊓ zpowers r = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rw [mem_bot]
    have h1 : orderOf x ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard (zpowers t) hx1
      rwa [Nat.card_zpowers, hto] at this
    have h2 : orderOf x ∣ 5 := by
      have := Subgroup.orderOf_dvd_natCard (zpowers r) hx2
      rwa [Nat.card_zpowers, hr5] at this
    have : orderOf x = 1 := by
      have := Nat.dvd_gcd h1 h2
      simpa using this
    exact orderOf_eq_one_iff.1 this
  have hZcard : Nat.card Z = 10 := by
    rw [hZ, card_sup_of_commute htr hZd, Nat.card_zpowers, Nat.card_zpowers, hto, hr5]
  have hAcard : Nat.card A = 60 := by
    rw [hA, Subgroup.card_map_of_injective hf, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hZA : Z ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxZ, hxA⟩
    rw [mem_bot]
    obtain ⟨σ, hσ, rfl⟩ := hxA
    have hcen : ∀ τ : Perm (Fin 5), τ * σ = σ * τ := fun τ => hf (by
      rw [map_mul, map_mul]
      exact (hZc _ hxZ (f τ)).symm)
    have hσ1 : σ = 1 := CFSG.perm_eq_one_of_forall_commute (by simp) fun τ => (hcen τ).symm
    rw [hσ1, map_one]
  have hZAc : ∀ z ∈ Z, ∀ a ∈ A, z * a = a * z := fun z hz a _ => hZc z hz a
  have hZAcard : Nat.card ↥(Z ⊔ A) = 600 := by
    rw [card_sup_of_commute hZAc hZA, hZcard, hAcard]
  have hQ₁card : Nat.card Q₁ * 2 = 1200 := by
    have := Subgroup.card_mul_index Q₁
    rwa [hQ₁, hQ] at this
  have hZQ₁ : Z ≤ Q₁ := sup_le (zpowers_le.2 htQ₁) (zpowers_le.2 hrQ₁)
  have hQ₁eq : Z ⊔ A = Q₁ :=
    Subgroup.eq_of_le_of_card_ge (sup_le hZQ₁ hAQ₁) (by omega)
  have huQ₁ : u ∈ Z ⊔ A := by rw [hQ₁eq]; exact hQL huL
  obtain ⟨z, hz, a, ha, hua⟩ := mem_sup_of_commute hZAc huQ₁
  have hz2 : z * z = 1 := by
    have h1 : z * z = (a * a)⁻¹ := by
      have h0 : (z * a) * (z * a) = 1 := by rw [← hua]; exact hu2
      have h00 : z * z * (a * a) = 1 := by
        calc z * z * (a * a) = z * (z * a) * a := by group
          _ = z * (a * z) * a := by rw [hZc z hz a]
          _ = (z * a) * (z * a) := by group
          _ = 1 := h0
      exact eq_inv_of_mul_eq_one_left h00
    have hzA : z * z ∈ Z ⊓ A := ⟨mul_mem hz hz, by
      rw [h1]; exact A.inv_mem (mul_mem ha ha)⟩
    rw [hZA, mem_bot] at hzA
    exact hzA
  obtain ⟨p, hp, s, hs, hzps⟩ := mem_sup_of_commute htr hz
  have hzt : z = 1 ∨ z = t := by
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hp
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hs
    have hr5' : r ^ 5 = 1 := by rw [← hr5]; exact pow_orderOf_eq_one r
    have hrs : r ^ (2 * n) = 1 := by
      have h1 : z * z = t ^ (2 * m) * r ^ (2 * n) := by
        rw [hzps]
        have hc : Commute t r := mem_center_iff.1 hr t
        calc t ^ m * r ^ n * (t ^ m * r ^ n) = t ^ m * t ^ m * (r ^ n * r ^ n) := by
              rw [mul_assoc, ← mul_assoc (r ^ n), (Commute.zpow_zpow hc.symm n m).eq, mul_assoc,
                ← mul_assoc]
          _ = t ^ (2 * m) * r ^ (2 * n) := by rw [← zpow_add, ← zpow_add]; ring_nf
      have h2 : t ^ (2 * m) = 1 := by
        rw [zpow_mul, show t ^ (2 : ℤ) = 1 by rw [zpow_two]; exact ht2, one_zpow]
      rw [h2, one_mul, hz2] at h1
      exact h1.symm
    have hrn : r ^ n = 1 := by
      have : r ^ n = (r ^ (2 * n)) ^ (3 : ℤ) := by
        rw [← zpow_mul]
        calc r ^ n = r ^ (5 * n) * r ^ n := by
              rw [show 5 * n = (5 : ℤ) * n from rfl, zpow_mul, show r ^ (5 : ℤ) = 1 by
                exact_mod_cast hr5', one_zpow, one_mul]
          _ = r ^ (2 * n * 3) := by rw [← zpow_add]; ring_nf
      rw [this, hrs, one_zpow]
    rw [hzps, hrn, mul_one]
    exact zpow_involution ht2 m
  rcases hzt with rfl | rfl
  · rw [one_mul] at hua
    rw [hua]
    have : A ≤ commutator Q := by
      calc A = ⁅A, A⁆ := hAperf.symm
        _ ≤ ⁅(⊤ : Subgroup Q), ⊤⁆ := commutator_mono le_top le_top
    exact this ha
  · exfalso
    apply htL
    have : z = u * a⁻¹ := by rw [hua]; group
    rw [this]
    exact QL.mul_mem huL (QL.inv_mem (hAQL ha))

end Main

end CFSG.EvenSporadicStandard.HSStd.FiveY
