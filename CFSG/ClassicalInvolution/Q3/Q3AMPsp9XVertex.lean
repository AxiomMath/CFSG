module

public import CFSG.ClassicalInvolution.Q3.Q3AMPsp9XAlpha

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer

section Route


variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem hyp51At_of_layers_wc [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hBelow : CITBelowU p f (Nat.card G)) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {s z₁ z₂ : G}
    (hA : IsElemAbelian 2 (Subgroup.closure ({z₁, z₂, s} : Set G)))
    (hA8 : Nat.card (Subgroup.closure ({z₁, z₂, s} : Set G)) = 8) (hs1 : s ≠ 1) (hz₁1 : z₁ ≠ 1)
    (hz₂1 : z₂ ≠ 1) (hz₁₂ : z₁ ≠ z₂) (hz₁s : z₁ ≠ s) (hz₂s : z₂ ≠ s) {L₁ L₂ : Subgroup G}
    (h₁ : IsSectionMember p f (Subgroup.centralizer ({s} : Set G)) L₁ z₁)
    (h₂ : IsSectionMember p f (Subgroup.centralizer ({s} : Set G)) L₂ z₂)
    (hwc : WeakClosureAt s L₁) (hnorm : NormalizesImageAt s z₂ L₁) :
    Hyp51At (Subgroup.closure ({z₁, z₂, s} : Set G)) s := by
  classical
  set B := Subgroup.closure ({z₁, z₂, s} : Set G) with hB
  have hsB : s ∈ B := Subgroup.subset_closure (by simp)
  have hz₁B : z₁ ∈ B := Subgroup.subset_closure (by simp)
  have hz₂B : z₂ ∈ B := Subgroup.subset_closure (by simp)
  have hZ : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
  have hsnc : ¬ ({s} : Set G) ⊆ Subgroup.center G := fun hs => hs1 (by
    have h1 : s ∈ Subgroup.center G := hs (Set.mem_singleton s)
    rwa [hZ, Subgroup.mem_bot] at h1)
  have hs := NDB.S.secData_sFamily h₁ h₂
  obtain ⟨D⟩ := hs.nonempty_lieSystem hBelow hsnc
  have key : ∀ L : Subgroup (OddQuot s), CFSG.IsComponent L → MovedByAll B s L →
      ∃ (j₀ : Fin D.card) (R₁ R₂ : Subgroup (compModel D j₀).K),
        NDB.S.SComponent B s z₁ z₂ L₁ L₂ hs.normalizes D j₀ R₁ R₂ := fun L hL hmov =>
    NDB.S.exists_sComponent hp2 hq hA hsB hz₁B hz₂B hs1 hz₁1 hz₂1 hz₁s hz₂s hz₁₂ h₁ h₂ D hL hmov
  refine ⟨fun L L' hL hL' hm hm' => ?_, fun L hL hm => ?_⟩
  · obtain ⟨j₀, R₁, R₂, hC⟩ := key L hL hm
    rw [hC.moved L hL hm, hC.moved L' hL' hm']
  · obtain ⟨j₀, R₁, R₂, hC⟩ := key L hL hm
    have hLe := hC.moved L hL hm
    rw [hLe] at hm ⊢
    exact alphaOf_moved_of_wc hp2 hq hA hA8 hs1 hz₁1 hz₂1 hz₁₂ h₁ h₂ hs.normalizes D j₀ R₁ R₂ hC
      hwc hnorm hm

end Route

end CFSG.ClassicalInvolution.Q3.Q3AM
