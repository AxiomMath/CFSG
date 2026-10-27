module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111E16

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

theorem agl81TenOneExists_of (h984 : AGL81NineEightFour G) (h84 : Asc81bEightFour)
    (hD2 : NoXBlockFor G) : AGL81TenOneExists G := by
  intro hS p P M H₁ R₁ he H₀ Q₀ hQ hQH hH₀ hH₀M hsyl hb3
  obtain ⟨hinf, -, hle⟩ := h984 hS p P M H₁ R₁ he H₀ Q₀ hQ hQH hH₀ hH₀M hsyl hb3
  have hglob : AGLGlobal G := aglGlobal_of_setting hS
  have hpair : TwoLocalPair M H₀ := ⟨he.maxTwoLocal_M, hH₀, hH₀M, hle⟩
  have h3 : TwoLocalPhaseThree M H₀ :=
    { hpair with
      charTwo_M := hglob.charTwo M he.maxTwoLocal_M.1
      twoCore_inf := hinf }
  exact h3.exists_weakSBlock (hpair.isKGroup_of_isKProper hglob.kProper).1 h84 hD2

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
