module

public import CFSG.LocalAnalysis.GH72.G3bFourOdd
public import CFSG.LocalAnalysis.GH72.G3bTwo
public import CFSG.LocalAnalysis.GH72.G3bSeven

public section

namespace CFSG.GH72

namespace Sec3Setting

variable {G : Type} [Group G] [Finite G]

theorem lemma_3_4 (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁)
    (h₂ : ∀ x ∈ 𝔖.S₂, ∀ y ∈ 𝔖.S₂, orderOf x = 2 → orderOf y = 2 → IsConj x y) :
    ∃ S₁' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' 𝔖.S₂ ∧
      ∃ n : ℕ, ∃ u ∈ Subgroup.normalizer ((𝔖.S : Subgroup G) : Set G), orderOf u = 3 ^ n ∧
        u ∈ Subgroup.normalizer (S₁' : Set G) ∧ u ∉ Subgroup.centralizer (S₁' : Set G) :=
  lemma_3_4_of_oddInput 𝔖 h₁ h₂ (lemma34OddInput_of 𝔖 h₁ h₂)

theorem prop_3_2 (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) :
    ∃ S₁' S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' S₂' ∧ HasProductFusion S₁' S₂' := by
  classical
  obtain ⟨S₂', hdd, hconj⟩ := lemma_3_3 𝔖 h₁
  let 𝔖' : Sec3Setting G := ⟨𝔖.S, 𝔖.S₁, S₂', hdd, 𝔖.noIndexTwo⟩
  exact prop_3_2_of_h34 𝔖' h₁ (lemma_3_4 𝔖' h₁ hconj)

theorem exists_productFusion (𝔖 : Sec3Setting G) :
    ∃ S₁' S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' S₂' ∧ HasProductFusion S₁' S₂' := by
  rcases 𝔖.decomp.dih₁.isKleinFour_or_isDihNonab with hK | hN
  · exact prop_3_2 𝔖 hK
  · exact prop_3_7 𝔖 hN

end Sec3Setting

end CFSG.GH72
