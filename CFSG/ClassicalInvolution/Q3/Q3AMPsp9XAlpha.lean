module

public import CFSG.ClassicalInvolution.Q3.Q3AMPsp9XTag
public import CFSG.ClassicalInvolution.SmallCases.NDB5eMain

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

theorem alphaOf_moved_of_wc (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {s z₁ z₂ : G}
    (hA : IsElemAbelian 2 (Subgroup.closure ({z₁, z₂, s} : Set G)))
    (hA8 : Nat.card (Subgroup.closure ({z₁, z₂, s} : Set G)) = 8) (hs1 : s ≠ 1) (hz₁1 : z₁ ≠ 1)
    (hz₂1 : z₂ ≠ 1) (hz₁₂ : z₁ ≠ z₂) {L₁ L₂ : Subgroup G}
    (h₁ : IsSectionMember p f (Subgroup.centralizer ({s} : Set G)) L₁ z₁)
    (h₂ : IsSectionMember p f (Subgroup.centralizer ({s} : Set G)) L₂ z₂)
    (hN : NormalizesLayer (NDB.S.sFamily s L₁ L₂) s)
    (D : LocalLieSystemAt p f (NDB.S.sFamily s L₁ L₂) s) (j₀ : Fin D.card)
    (R₁ R₂ : Subgroup (compModel D j₀).K)
    (hSC : NDB.S.SComponent (Subgroup.closure ({z₁, z₂, s} : Set G)) s z₁ z₂ L₁ L₂ hN D j₀ R₁ R₂)
    (hwc : WeakClosureAt s L₁) (hnorm : NormalizesImageAt s z₂ L₁)
    (hmov : MovedByAll (Subgroup.closure ({z₁, z₂, s} : Set G)) s
      (secComponentHom hN D j₀).range) :
    alphaOf (inducedImage (secComponentHom hN D j₀).range
      (modOdd s (Subgroup.closure ({z₁, z₂, s} : Set G)))) = ⊥ := by
  have htag := tag_of_sComponent_wc hp2 hq hN D j₀ R₁ R₂ hSC hwc
  have hz₁R : ∀ h, oddQuotMk s ⟨z₁, h⟩ ∈ (secComponentHom hN D j₀).range :=
    fun h => Subgroup.map_le_range _ R₁ (hSC.img₁ ▸ hSC.mem₁ h)
  have hz₂R : ∀ h, oddQuotMk s ⟨z₂, h⟩ ∈ (secComponentHom hN D j₀).range :=
    fun h => Subgroup.map_le_range _ R₂ (hSC.img₂ ▸ hSC.mem₂ h)
  have hU₁ : ∀ h, IsUniqueInvolution (modOdd s L₁) (oddQuotMk s ⟨z₁, h⟩) := fun h =>
    NDB.S.isUniqueInvolution_modOdd_of_sec hp2 hq h₁ h
  have hU₂ : ∀ h, IsUniqueInvolution (modOdd s L₂) (oddQuotMk s ⟨z₂, h⟩) := fun h =>
    NDB.S.isUniqueInvolution_modOdd_of_sec hp2 hq h₂ h
  rcases htag with ⟨ht, hn⟩ | ⟨ht, hn⟩ | ht | ht
  · exact NDB.Alpha.alpha_toral hp2 hq hA hA8 hs1 hN D j₀ (Or.inl ht)
      (fun h => absurd (hn.symm.trans h.2) (by decide)) hSC.ker hSC.fund₁ hSC.fund₂ hSC.img₁
      hSC.img₂ hU₁ hU₂ hnorm hmov
  · exact NDB.Alpha.alpha_toral hp2 hq hA hA8 hs1 hN D j₀ (Or.inr ht)
      (fun h => absurd (ht.symm.trans h.1) (by decide)) hSC.ker hSC.fund₁ hSC.fund₂ hSC.img₁
      hSC.img₂ hU₁ hU₂ hnorm hmov
  · exact NDB.Alpha.alpha_g2d4 hp2 hq hA hz₁1 hz₂1 hz₁₂ hN D j₀ (Or.inl ht) hz₁R hz₂R
  · exact NDB.Alpha.alpha_g2d4 hp2 hq hA hz₁1 hz₂1 hz₁₂ hN D j₀ (Or.inr ht) hz₁R hz₂R

end Route

end CFSG.ClassicalInvolution.Q3.Q3AM
