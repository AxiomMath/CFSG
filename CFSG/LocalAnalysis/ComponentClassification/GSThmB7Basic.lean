module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace Seven

variable {X : Type} [Group X]

@[expose] def IsSylowIn (S Y : Subgroup X) : Prop :=
  S ≤ Y ∧ ∃ R : Sylow 2 ↥Y, (R : Subgroup ↥Y) = S.subgroupOf Y

variable [Finite X]

omit [Finite X] in
theorem IsSylowIn.isPGroup {S Y : Subgroup X} (hS : IsSylowIn S Y) : IsPGroup 2 S := by
  obtain ⟨hSY, R, hR⟩ := hS
  have h1 := R.isPGroup'.map Y.subtype
  rwa [hR, map_subgroupOf_eq_of_le hSY] at h1

theorem exists_normalizer_conj_of_central {S : Subgroup X}
    (hS : ∃ R : Sylow 2 X, (R : Subgroup X) = S) {s g : X}
    (hs : ∀ y ∈ S, y * s = s * y) (hgs : ∀ y ∈ S, y * (g⁻¹ * s * g) = (g⁻¹ * s * g) * y) :
    ∃ n ∈ normalizer (S : Set X), g⁻¹ * s * g = n⁻¹ * s * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := hS
  have h1 : s ∈ centralizer (R : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact hs y (hR ▸ hy)
  have h2 : g⁻¹ * s * g ∈ centralizer (R : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact hgs y (hR ▸ hy)
  obtain ⟨n, hn, hn'⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer R s g h1 h2
  exact ⟨n, hR ▸ hn, hn'⟩

theorem exists_sylow_of_normalizer_le {S Y : Subgroup X} (hS : IsSylowIn S Y)
    (hN : normalizer (S : Set X) ≤ Y) : ∃ R : Sylow 2 X, (R : Subgroup X) = S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSY, RY, hRY⟩ := hS
  have hS2 : IsPGroup 2 S := IsSylowIn.isPGroup ⟨hSY, RY, hRY⟩
  obtain ⟨R, hR⟩ := hS2.exists_le_sylow
  have hSR : S = R := by
    by_contra hne
    have hlt : S.subgroupOf R < ⊤ := by
      refine lt_of_le_of_ne le_top fun he => hne (le_antisymm hR ?_)
      intro y hy
      have : (⟨y, hy⟩ : R) ∈ S.subgroupOf R := he ▸ mem_top _
      exact this
    have hnil : Group.IsNilpotent R := R.isPGroup'.isNilpotent
    obtain ⟨⟨w, hwR⟩, hwN, hwS⟩ := Set.exists_of_ssubset
      (Group.normalizerCondition_of_isNilpotent _ hlt)
    have hwN' : w ∈ normalizer (S : Set X) := by
      rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have hyR : y ∈ (R : Subgroup X) := hR hy
        have := (mem_normalizer_iff.mp hwN ⟨y, hyR⟩).mp hy
        exact this
      · intro hy
        have hyR : y ∈ (R : Subgroup X) := by
          have h1 : w * y * w⁻¹ ∈ (R : Subgroup X) := hR hy
          have h2 := mul_mem (mul_mem (inv_mem hwR) h1) hwR
          rwa [show w⁻¹ * (w * y * w⁻¹) * w = y by group] at h2
        exact (mem_normalizer_iff.mp hwN ⟨y, hyR⟩).mpr hy
    have hwY : w ∈ Y := hN hwN'
    have hle : S.subgroupOf Y ≤ (S ⊔ zpowers w).subgroupOf Y := fun y hy =>
      mem_subgroupOf.mpr (mem_sup_left (mem_subgroupOf.mp hy))
    have h2 : IsPGroup 2 ((S ⊔ zpowers w).subgroupOf Y) := by
      have hsub : S ⊔ zpowers w ≤ (R : Subgroup X) := sup_le hR (zpowers_le.mpr hwR)
      exact (R.isPGroup'.to_le hsub).comap_subtype
    have heq := RY.is_maximal' h2 (hRY ▸ hle)
    have hwS' : w ∈ S := by
      have : (⟨w, hwY⟩ : Y) ∈ (S ⊔ zpowers w).subgroupOf Y :=
        mem_subgroupOf.mpr (mem_sup_right (mem_zpowers w))
      rw [heq, hRY] at this
      exact this
    exact hwS hwS'
  exact ⟨R, hSR.symm⟩

end Seven

end CFSG.ComponentClassification.GSThmB
