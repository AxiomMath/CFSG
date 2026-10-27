module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ChainNine
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoFalse
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactA9NotInvolvedGL4Holds

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup

theorem agl81FourteenFifteen_of_caseOne
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (h96 : NineSixMoreoverGen)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen)
    (hinv : KFactL34NotInvolvedA11)
    (hC1 : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty → CaseOneFalse M)
    (hKF : KFactA11GammaTwoSet) (h514 : FiveFourteenA11Use) (h525 : FiveTwentyFiveS11Use)
    (h73 : SevenThreeInput)
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne)
    (hX : ∀ (G : Type) [Group G] [Finite G], CStarGen G →
      CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (h1453 : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty → FourteenFiveThreeAt M) :
    AGL81FourteenFifteen := by
  refine agl81FourteenFifteen_of_choice h1210 h1211 h97 h96 hS h991 hinv ?_
  intro G _ _ hC M hM hσ
  have hU : NineNineOneAt M := nineNineOneAt_of_twelveEleven h991 h1211
  have hpre : PreambleTypes M :=
    preambleTypes_of h1211 hC hM hσ (preambleFiveTypes_of h1210 h97 h96 hC hM hσ hU)
  have hL : PLayerNotLeAt M := pLayerNotLeAt_of h1211 h1210 h97 hU
  exact ⟨hC1 G hC M hM hσ,
    caseTwoFalse_of hpre hU hL hKF h514 h525 (hX G hC) h73 h711
      (h1453 G hC M hM hσ) kFactA9NotInvolvedGL4_holds⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
