module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open MulAction Subgroup

private theorem sylow_subgroupOf {G : Type} [Group G] {C : Subgroup G} (S : Sylow 2 G)
    (hS : (S : Subgroup G) ≤ C) :
    ∃ T : Sylow 2 C, ∀ x : C, x ∈ (T : Subgroup C) ↔ (x : G) ∈ (S : Subgroup G) :=
  ⟨S.subtype hS, fun _ => Iff.rfl⟩

private theorem mem_smul_sylow_iff {H : Type} [Group H] (T : Sylow 2 H) (c x : H) :
    x ∈ ((c • T : Sylow 2 H) : Subgroup H) ↔ c⁻¹ * x * c ∈ (T : Subgroup H) := by
  rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem exists_conj_sylow_centralizer {G : Type} [Group G] [Finite G] {z : G} (S₁ S₂ : Sylow 2 G)
    (h₁ : ∀ s ∈ (S₁ : Subgroup G), s * z = z * s) (h₂ : ∀ s ∈ (S₂ : Subgroup G), s * z = z * s) :
    ∃ c : G, c * z = z * c ∧ ∀ x ∈ (S₁ : Subgroup G), c * x * c⁻¹ ∈ (S₂ : Subgroup G) := by
  have hmem : ∀ g : G, g ∈ centralizer ({z} : Set G) ↔ g * z = z * g := fun g => by
    rw [mem_centralizer_iff]
    simp [eq_comm]
  obtain ⟨T₁, hT₁⟩ := sylow_subgroupOf S₁ fun s hs => (hmem s).2 (h₁ s hs)
  obtain ⟨T₂, hT₂⟩ := sylow_subgroupOf S₂ fun s hs => (hmem s).2 (h₂ s hs)
  obtain ⟨c, hc⟩ := exists_smul_eq (centralizer ({z} : Set G)) T₁ T₂
  refine ⟨c, (hmem c).1 c.2, fun x hx => ?_⟩
  have hx' : (⟨x, (hmem x).2 (h₁ x hx)⟩ : centralizer ({z} : Set G)) ∈ (T₁ : Subgroup _) :=
    (hT₁ _).2 hx
  have h3 : c * ⟨x, (hmem x).2 (h₁ x hx)⟩ * c⁻¹ ∈ ((c • T₁ : Sylow 2 _) : Subgroup _) := by
    rw [mem_smul_sylow_iff]
    simpa [mul_assoc] using hx'
  rw [hc] at h3
  exact (hT₂ _).1 h3

theorem exists_conj_into_sylow {G : Type} [Group G] [Finite G] {C : Subgroup G} (S : Sylow 2 G)
    (hS : (S : Subgroup G) ≤ C) {t : G} (ht : t ∈ C) (ht2 : t * t = 1) :
    ∃ c ∈ C, c⁻¹ * t * c ∈ (S : Subgroup G) := by
  obtain ⟨T, hT⟩ := sylow_subgroupOf S hS
  have ht' : (⟨t, ht⟩ : C) * ⟨t, ht⟩ = 1 := Subtype.ext ht2
  have hord : orderOf (⟨t, ht⟩ : C) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have hP : IsPGroup 2 (zpowers (⟨t, ht⟩ : C)) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rwa [Nat.card_zpowers, pow_one]
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨c, hc⟩ := exists_smul_eq C T Q
  have h1 : (⟨t, ht⟩ : C) ∈ ((c • T : Sylow 2 C) : Subgroup C) := hc ▸ hQ (mem_zpowers _)
  rw [mem_smul_sylow_iff] at h1
  exact ⟨c, c.2, (hT _).1 h1⟩

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
