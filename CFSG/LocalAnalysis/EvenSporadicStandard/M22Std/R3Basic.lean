module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

variable {G : Type} [Group G]

theorem zpow_invol_cases {w : G} (hw2 : w * w = 1) (n : ℤ) : w ^ n = 1 ∨ w ^ n = w := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [zpow_mul, zpow_two, hw2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hw2, one_zpow, one_mul]

theorem mem_sup_zpowers_invol {A : Subgroup G} {w : G} (hw2 : w * w = 1)
    (hwN : ∀ a, a ∈ A ↔ w * a * w⁻¹ ∈ A) {k : G} (hk : k ∈ A ⊔ zpowers w) :
    k ∈ A ∨ ∃ a ∈ A, k = w * a := by
  have hle : zpowers w ≤ normalizer (A : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_normalizer_iff.2 hwN)
  have h := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers w) A hle
  rw [sup_comm] at hk
  have hk' : k ∈ ((zpowers w ⊔ A : Subgroup G) : Set G) := hk
  rw [h] at hk'
  obtain ⟨c, hc, a, ha, rfl⟩ := hk'
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  rcases zpow_invol_cases hw2 n with h1 | h1
  · left
    simpa [h1] using ha
  · right
    exact ⟨a, ha, by simp [h1]⟩

theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) =
      Nat.card A * Nat.card B := by
  set N := normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have key : ∀ (A' B' : Subgroup N) [A'.Normal],
      Nat.card (A' ⊔ B' : Subgroup N) * Nat.card (A' ⊓ B' : Subgroup N) =
        Nat.card A' * Nat.card B' := by
    intro A' B' _
    have h1 := Subgroup.relIndex_mul_card (H := A') (K := A' ⊔ B')
    rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
    have h2 := Subgroup.relIndex_mul_card (H := A') (K := B')
    rw [← h1, ← h2]
    ring
  have h := key (A.subgroupOf N) (B.subgroupOf N)
  have hc : ∀ Y : Subgroup G, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hsup : A.subgroupOf N ⊔ B.subgroupOf N = (A ⊔ B).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAN, inf_eq_left.mpr hB,
      inf_eq_left.mpr (sup_le hAN hB)]
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  exact h

theorem card_zpowers_invol {w : G} (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    Nat.card (zpowers w) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1]

theorem card_sup_zpowers_invol {A : Subgroup G} {w : G} (hw2 : w * w = 1)
    (hwN : ∀ a, a ∈ A ↔ w * a * w⁻¹ ∈ A) (hwA : w ∉ A) :
    Nat.card ↥(A ⊔ zpowers w) = 2 * Nat.card A := by
  have hle : zpowers w ≤ normalizer (A : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_normalizer_iff.2 hwN)
  have h := card_sup_mul_card_inf_of_le_normalizer hle
  have hw1 : w ≠ 1 := fun h1 => hwA (h1 ▸ A.one_mem)
  have hbot : A ⊓ zpowers w = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxw⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxw
    rcases zpow_invol_cases hw2 n with h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · exact absurd (h1 ▸ hxA) hwA
  rw [hbot, Subgroup.card_bot, mul_one, card_zpowers_invol hw2 hw1] at h
  rw [h]
  ring

theorem mem_map_conj {K : Subgroup G} (g x : G) :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem normalizes_of_centralizes {A : Subgroup G} {w : G} (hw : ∀ a ∈ A, w * a = a * w) :
    ∀ a, a ∈ A ↔ w * a * w⁻¹ ∈ A := by
  intro a
  constructor
  · intro ha
    rw [hw a ha]
    simpa using ha
  · intro ha
    have h := hw _ ha
    have h2 : w * a * w⁻¹ = a := by
      calc w * a * w⁻¹ = w⁻¹ * (w * (w * a * w⁻¹)) := by group
        _ = w⁻¹ * ((w * a * w⁻¹) * w) := by rw [h]
        _ = a := by group
    rwa [h2] at ha

variable [Finite G]

theorem exists_conj_sylow_two {C P₁ P₂ : Subgroup G}
    (h₁ : P₁ ≤ C ∧ IsPGroup 2 P₁ ∧ ¬ 2 ∣ P₁.relIndex C)
    (h₂ : P₂ ≤ C ∧ IsPGroup 2 P₂ ∧ ¬ 2 ∣ P₂.relIndex C) :
    ∃ g ∈ C, ∀ x, x ∈ P₂ ↔ g⁻¹ * x * g ∈ P₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP₁C, hP₁p, hidx₁⟩ := h₁
  obtain ⟨hP₂C, hP₂p, hidx₂⟩ := h₂
  have hp₁ : IsPGroup 2 (P₁.subgroupOf C) :=
    hP₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hP₁C).symm
  have hp₂ : IsPGroup 2 (P₂.subgroupOf C) :=
    hP₂p.of_equiv (Subgroup.subgroupOfEquivOfLe hP₂C).symm
  let S₁ : Sylow 2 ↥C := hp₁.toSylow hidx₁
  let S₂ : Sylow 2 ↥C := hp₂.toSylow hidx₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C S₁ S₂
  refine ⟨g, g.2, fun x => ?_⟩
  by_cases hx : x ∈ C
  · have h1 : (⟨x, hx⟩ : ↥C) ∈ (S₂ : Subgroup ↥C) ↔ g⁻¹ * ⟨x, hx⟩ * g ∈ (S₁ : Subgroup ↥C) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [mul_assoc]
    have e1 : (⟨x, hx⟩ : ↥C) ∈ (S₂ : Subgroup ↥C) ↔ x ∈ P₂ := Subgroup.mem_subgroupOf
    have e2 : g⁻¹ * ⟨x, hx⟩ * g ∈ (S₁ : Subgroup ↥C) ↔ (g : G)⁻¹ * x * g ∈ P₁ :=
      Subgroup.mem_subgroupOf (H := P₁) (K := C) (h := g⁻¹ * ⟨x, hx⟩ * g)
    rw [← e1, h1]
    exact e2
  · have hxP₂ : x ∉ P₂ := fun h => hx (hP₂C h)
    have hxP₁ : (g : G)⁻¹ * x * g ∉ P₁ := fun h => hx (by
      have := C.mul_mem (C.mul_mem g.2 (hP₁C h)) (C.inv_mem g.2)
      simpa [mul_assoc] using this)
    exact ⟨fun h => absurd h hxP₂, fun h => absurd h hxP₁⟩

end CFSG.EvenSporadicStandard.M22Std
