module

public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def orbitConjugates (B K : Subgroup G) : Set (Subgroup G) :=
  {M | ∃ b ∈ B, M = CFSG.conjugate K b}

theorem map_conj_eq_self_iff {K : Subgroup G} {g : G} :
    K.map (MulAut.conj g).toMonoidHom = K ↔ g ∈ normalizer (K : Set G) := by
  constructor
  · intro h
    rw [mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      rw [← h]
      exact ⟨k, hk, rfl⟩
    · intro hk
      rw [← h] at hk
      obtain ⟨k', hk', hkk⟩ := hk
      have : k' = k := by simpa [MulAut.conj_apply] using hkk
      rwa [← this]
  · intro hg
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact (mem_normalizer_iff.mp hg k).mp hk
    · intro k hk
      have hk' : g⁻¹ * k * g ∈ K := by
        simpa using (mem_normalizer_iff.mp (inv_mem hg) k).mp hk
      refine ⟨g⁻¹ * k * g, hk', ?_⟩
      change g * (g⁻¹ * k * g) * g⁻¹ = k
      group

end CFSG.LocalAnalysis.GorensteinLyons
