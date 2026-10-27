module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWNon

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer

theorem exists_eight_not_isolated {G : Type} [Group G] [Finite G] {a x : G} {J S : Subgroup G}
    (hset : L34Sec4Setting G a x J S) (h3 : IsThreeConnected (S ⊓ withKernel J)) :
    ∃ F : Subgroup G, F ≤ S ⊓ J ∧ IsEightGroup F ∧
      ∃ s ∈ S ⊓ withKernel J, s * s = 1 ∧ (∀ e ∈ F, s * e = e * s) ∧ s ∉ F := by
  obtain ⟨-, hU3, hL34, -, hSyl, -, -⟩ := id hset
  obtain ⟨-, -, -, hJa, hJc, -, -⟩ := hU3
  have hJper : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJa hJc
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hSyl
  obtain ⟨D⟩ := exists_wStd hJper hL34 (GrS4.isSylowTwoIn_inf hSyl) hSyl.1
  obtain ⟨F₁, F₂, hF₁S, hF₂S, hF₁, hF₂, hne⟩ := D.exists_two_eights hS2
  have hPS₁ : S ⊓ J ≤ S ⊓ withKernel J := inf_le_inf_left _ le_sup_left
  exact ⟨F₁, hF₁S, hF₁, exists_not_isolated_of_threeConnected h3 (hF₁S.trans hPS₁)
    (hF₂S.trans hPS₁) hF₁ hF₂ hne (hF₁S.trans hPS₁) hF₁⟩

end CFSG.ComponentClassification.GrSLit.GrS5S
