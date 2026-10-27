module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ChainCaseTwo
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFalse
import CFSG.LocalAnalysis.AGL81TheoremCD.RankFour.TheoremCOfD

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup

theorem agl81FourteenFifteen_of_caseOneInputs
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (h96 : NineSixMoreoverGen)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen)
    (hinv : KFactL34NotInvolvedA11)
    (h142 : FourteenTwoCaseOneGen) (h143 : FourteenThreeCaseOneGen)
    (h145 : FourteenFiveCaseOneGen)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (h7145 : CFSG.LocalAnalysis.RankThreeUC.S15.K7145)
    (h1410 : KFact1410a) (h4143 : K4143NoExtraspecial)
    (hKF : KFactA11GammaTwoSet) (h514 : FiveFourteenA11Use) (h525 : FiveTwentyFiveS11Use)
    (h73 : SevenThreeInput)
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne)
    (hX : ∀ (G : Type) [Group G] [Finite G], CStarGen G →
      CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (h1453 : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty → FourteenFiveThreeAt M) :
    AGL81FourteenFifteen := by
  refine agl81FourteenFifteen_of_caseOne h1210 h1211 h97 h96 hS h991 hinv ?_
    hKF h514 h525 h73 h711 hX h1453
  exact caseOneFalse_gen h142 h143 h145 hFF h7145 h1410 h4143 (by
    intro G _ _ hC M hM hσ
    have hU : NineNineOneAt M := nineNineOneAt_of_twelveEleven h991 h1211
    have hpre : PreambleTypes M :=
      preambleTypes_of h1211 hC hM hσ (preambleFiveTypes_of h1210 h97 h96 hC hM hσ hU)
    have hL : PLayerNotLeAt M := pLayerNotLeAt_of h1211 h1210 h97 hU
    exact ⟨hpre, hU, hL⟩)

theorem agl81TheoremCFour_of_caseOneInputs
    (hD : CFSG.Yardstones.Mf4cdcdf2e013.AGL81TheoremDFour)
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (h96 : NineSixMoreoverGen)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen)
    (hinv : KFactL34NotInvolvedA11)
    (h142 : FourteenTwoCaseOneGen) (h143 : FourteenThreeCaseOneGen)
    (h145 : FourteenFiveCaseOneGen)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (h7145 : CFSG.LocalAnalysis.RankThreeUC.S15.K7145)
    (h1410 : KFact1410a) (h4143 : K4143NoExtraspecial)
    (hKF : KFactA11GammaTwoSet) (h514 : FiveFourteenA11Use) (h525 : FiveTwentyFiveS11Use)
    (h73 : SevenThreeInput)
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne)
    (hX : ∀ (G : Type) [Group G] [Finite G], CStarGen G →
      CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (h1453 : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty → FourteenFiveThreeAt M) :
    CFSG.Yardstones.Mf4cdcdf2e013.AGL81TheoremCFour :=
  CFSG.LocalAnalysis.AGL81TheoremCD.RankFour.agl81TheoremCFour_of_theoremDFour hD
    (agl81FourteenFifteen_of_caseOneInputs h1210 h1211 h97 h96 hS h991 hinv
      h142 h143 h145 hFF h7145 h1410 h4143 hKF h514 h525 h73 h711 hX h1453)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
