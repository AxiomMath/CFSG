module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFifteenOne
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.StepSeven
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.InnerOnK
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactL34FixedPointsProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.LemmaU3

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

theorem agl81FourteenFifteen_of_step7
    (h : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
        PreambleTypes M ∧ ChoiceExists M ∧ CaseOneFalse M ∧ CaseTwoFalse M ∧
        KTwoComponentAt M ∧ KNormalAt M ∧ PLayerNotLeAt M ∧ NineNineOneAt M) :
    AGL81FourteenFifteen := by
  refine agl81FourteenFifteen_of_kFact kFactL34FixedPointsGen ?_
  intro G _ _ hC M hM hσ
  obtain ⟨hpre, hch, h1, h2, hTwo, hK, hL, hU⟩ := h G hC M hM hσ
  have h14 : ∀ H ∈ H2StarAll M, CaseThree M H := caseThree_of_cases hpre hch h1 h2
  exact ⟨hpre, hch, h1, h2, fourteenFifteenNormAt_of hpre h14 hTwo hK hL, hK, hL, hU⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
