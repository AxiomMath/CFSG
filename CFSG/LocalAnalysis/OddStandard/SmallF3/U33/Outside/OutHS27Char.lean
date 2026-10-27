module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutHS27Fix

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

private theorem hs27_index_commAut {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T) {t : T}
    (ht : orderOf t = 2) (hC : Nonempty (↥(centralizer ({t} : Set T)) ≃* E2 3))
    {α : MulAut T} (hα1 : α ≠ 1) (hα3 : ∃ n : ℕ, orderOf α = 3 ^ n) (hαt : α t = t) :
    (commAut α).index = 2 := by
  have hcard := hs27_card_T hT ht hC hα1 hα3 hαt
  have h1 : Nat.card ↥(commAut α) * (commAut α).index = Nat.card ↥(commAut α) * 2 := by
    rw [Subgroup.card_mul_index, hcard]
    ring
  exact Nat.mul_left_cancel Nat.card_pos h1

theorem hs27_abelian_not_le_card {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T) {t : T}
    (ht : orderOf t = 2) (hC : Nonempty (↥(centralizer ({t} : Set T)) ≃* E2 3))
    {α : MulAut T} (hα1 : α ≠ 1) (hα3 : ∃ n : ℕ, orderOf α = 3 ^ n) (hαt : α t = t)
    (hab : ∀ a ∈ commAut α, ∀ b ∈ commAut α, a * b = b * a) (A : Subgroup T)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAT : ¬ A ≤ commAut α) : Nat.card A ≤ 8 := by
  classical
  obtain ⟨hTn, hinf, hsup, hY⟩ := iv2_2_7 T hT t ht hC α hα1 hα3 hαt
  haveI : (commAut α).Normal := hTn
  have hindex : (commAut α).index = 2 := hs27_index_commAut hT ht hC hα1 hα3 hαt
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  obtain ⟨a, haA, haT⟩ := Set.not_subset.mp hAT
  have hasup : a ∈ commAut α ⊔ Subgroup.zpowers t := by rw [hsup]; trivial
  obtain ⟨y, hyT, z, hzK, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hasup
  have hz : z = 1 ∨ z = t := by
    have hzmem : z ∈ (Finset.range 2).image (fun i => t ^ i) := by
      have h := hzK
      rw [mem_zpowers_iff_mem_range_orderOf, ht] at h
      exact h
    obtain ⟨i, hi, hiz⟩ := Finset.mem_image.mp hzmem
    rw [Finset.mem_range] at hi
    interval_cases i
    · left; simpa using hiz.symm
    · right; simpa using hiz.symm
  have hle : A ⊓ commAut α ≤ Subgroup.centralizer ({t} : Set T) ⊓ commAut α := by
    intro x hx
    obtain ⟨hxA, hxT⟩ := Subgroup.mem_inf.mp hx
    have hxt : x * t = t * x := by
      rcases hz with hz1 | hzt
      · exfalso
        apply haT
        rw [← hyz, hz1, mul_one]
        exact hyT
      · have hcomm_a : x * (y * t) = (y * t) * x := by
          have h := hA x hxA a haA
          rw [← hyz, hzt] at h
          exact h
        have h1 : y * (x * t) = x * (y * t) := by
          rw [← mul_assoc x y t, hab x hxT y hyT]; group
        have h2 : (y * t) * x = y * (t * x) := by group
        exact mul_left_cancel (by rw [h1, hcomm_a, h2])
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hxt, hxT⟩
  have hcard_inf : Nat.card ↥(A ⊓ commAut α) ≤ 4 := by
    calc Nat.card ↥(A ⊓ commAut α)
        ≤ Nat.card ↥(Subgroup.centralizer ({t} : Set T) ⊓ commAut α) :=
          Subgroup.card_le_of_le hle
      _ = 4 := hs27_card_cent_inter hT ht hC hα1 hα3 hαt
  have hcardH : Nat.card ↥((commAut α).subgroupOf A) = Nat.card ↥(commAut α ⊓ A) := by
    rw [← Subgroup.card_subtype A ((commAut α).subgroupOf A), Subgroup.subgroupOf_map_subtype]
  have hdvd : ((commAut α).subgroupOf A).index ∣ 2 := by
    have h := Subgroup.relIndex_dvd_index_of_normal (H := commAut α) (K := A)
    rw [hindex] at h
    exact h
  have hindex_le : ((commAut α).subgroupOf A).index ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have h2 : Nat.card ↥(commAut α ⊓ A) = Nat.card ↥(A ⊓ commAut α) := by rw [inf_comm]
  have hcardA : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ commAut α) := by
    have h1 : Nat.card A =
        Nat.card ↥((commAut α).subgroupOf A) * ((commAut α).subgroupOf A).index :=
      (Subgroup.card_mul_index ((commAut α).subgroupOf A)).symm
    calc Nat.card A
        = Nat.card ↥((commAut α).subgroupOf A) * ((commAut α).subgroupOf A).index := h1
      _ = Nat.card ↥(commAut α ⊓ A) * ((commAut α).subgroupOf A).index := by rw [hcardH]
      _ ≤ Nat.card ↥(commAut α ⊓ A) * 2 := Nat.mul_le_mul_left _ hindex_le
      _ = 2 * Nat.card ↥(A ⊓ commAut α) := by rw [h2]; ring
  calc Nat.card A ≤ 2 * Nat.card ↥(A ⊓ commAut α) := hcardA
    _ ≤ 2 * 4 := Nat.mul_le_mul_left 2 hcard_inf
    _ = 8 := by norm_num

theorem hs27_char_abelian {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T) {t : T}
    (ht : orderOf t = 2) (hC : Nonempty (↥(centralizer ({t} : Set T)) ≃* E2 3))
    {α : MulAut T} (hα1 : α ≠ 1) (hα3 : ∃ n : ℕ, orderOf α = 3 ^ n) (hαt : α t = t)
    (hab : ∀ a ∈ commAut α, ∀ b ∈ commAut α, a * b = b * a)
    (h16 : 16 ≤ Nat.card ↥(commAut α)) : (commAut α).Characteristic := by
  classical
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  have hAab : ∀ a ∈ (commAut α).map φ.toMonoidHom,
      ∀ b ∈ (commAut α).map φ.toMonoidHom, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hab x hx y hy]
  have hcard : Nat.card ↥((commAut α).map φ.toMonoidHom) = Nat.card ↥(commAut α) :=
    Subgroup.card_map_of_injective φ.injective
  have hle : (commAut α).map φ.toMonoidHom ≤ commAut α := by
    by_contra h
    have hsmall := hs27_abelian_not_le_card hT ht hC hα1 hα3 hαt hab _ hAab h
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
