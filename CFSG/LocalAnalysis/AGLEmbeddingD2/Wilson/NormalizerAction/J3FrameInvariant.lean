module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3F0Subgroups
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverFrame

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.RankThree.Asc83Table CFSG.RankThree.PartTwo CFSG.Blueprint Subgroup

variable
  (hchk : GammaWordFacts)
include hchk

theorem frame_invariant_subgroups {X : Type} [Group X] [Finite X] (hX : CFSG.IsQuasisimple X)
    (hZ3 : Nat.card (center X) = 3) (e : X ⧸ center X ≃* NativeSporadic.J3)
    {F : Subgroup X} (hF : IsElementaryAbelian 3 (F.map (QuotientGroup.mk' (center X))))
    (hZF : center X ≤ F) (hF81 : Nat.card F = 81) :
    ∃ F₁ : Subgroup X, center X ≤ F₁ ∧ F₁ ≤ F ∧ Nat.card F₁ = 27 ∧
      (∀ y ∈ normalizer (F : Set X), ∀ s ∈ F₁, y * s * y⁻¹ ∈ F₁) ∧
      ∀ S : Subgroup X, S ≤ F → (∀ y ∈ normalizer (F : Set X), ∀ s ∈ S, y * s * y⁻¹ ∈ S) →
        S = ⊥ ∨ S = center X ∨ S = F₁ ∨ S = F := by
  obtain ⟨k, hk, hFk, hnorm⟩ := j3_frame hchk hX hZ3 e hF hZF hF81
  subst hFk
  have hcen := hk.zpowers_xB3_eq_center hZ3
  refine ⟨F1 k, ?_, hk.F1_le_F0, hk.card_F1, fun y hy s hs => hk.conj_F1 y (hnorm y hy) s hs, ?_⟩
  · rw [← hcen, Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  · intro S hSF hS
    rw [← hcen]
    exact hk.invariant_F0 S hSF fun y hy s hs =>
      hS y (hk.closure_le_normalizer hy) s hs

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
