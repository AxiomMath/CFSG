module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4HoldsE3
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongE3K2Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622Final
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622Exit
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDEvenHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291ConsumersHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614ForP622
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact131Holds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactReeBorel
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactJ1L27
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKG2024Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2024
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401ThreeMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2314Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2715
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401Spor
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxBridge
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutOdd
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDAssemble
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3RankHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3J1Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3ParabolicHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3L3U3Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3L2Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongK64ii
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDOddHolds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614 (KFact64ii KFact64iiThree KFact292
  slotP614Core_of_kFact64ii slotP614CaseDelta_of_open p622CaseDelta4_holds)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD (s622KFactD_of_kfacts)

section FrontierE3

theorem gl83SmallRankProp622_of_frontierE3
    (hKP1 : KFactP65RankThree)
    (hcoreL : SlotP614CoreLargeU0) (hEven5 : KFactFieldAutEven)
    (hD : KFactDihedralTypeAut) (h27 : KFactReeL28) (h1019 : KFact1019) (h2025 : KFact2025)
    (hgen : KFactParabolicGen) (hcov : KFactParabolicCover) (hloc : KFactSporLocal) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G →
      FullCoreLocal G → GL83SmallRankProp622 G :=
  gl83SmallRankProp622_of_kfacts3 kFactBlockFactorThreePrime_of_cgtBlock
    gl83SmallRankLemma62At3_proved (KFactProofs.RankTwoUniq.kFactRankTwoUniqueness_of_core
        KFactProofs.RankTwoUniq.k1Core_holds)
    kfactRankThreeStructure_proved Parrott.P614.slotP614CaseDelta_holds
    (slotP614Core_of_kFact64ii FongK64ii.kFact64ii_holds) slotP614NormalizerRankLarge_holds
    slotP614StepL617Large_holds slotP614OmegaULarge_holds hcoreL
    kFactFieldAutEvenAt_three_holds kFactFieldAutOddAt_three_holds
    (s622KFactD_of_kfacts hEven5 kFactFieldAutOdd_holds) FongK64ii.kFact64ii_holds p622CaseDelta4_holds
    (stepP65OddE3U0_of_kfactsE3 hKP1.toS kFactP65RankTwoS_holds) p622L27Exit_holds kFact2713Three_holds kFactL3U3SL2Three_holds
    kFactParabolicSectionThree_holds kFactJ1ClosureThree_holds kFactThreeRankTwo_holds p622L613_holds hD
    kFactReeSylowTwo_holds h27 kFactReeBorel_holds (kFact2024_of_kg2024 kg2024_holds)
    kFact2401Three_holds kFact2314_holds h1019 h2025 kFact131_holds hgen kFact2715_holds hcov
    kFactSporThree_holds kFact2401Spor_holds hloc kFactJ1Sylow_holds kFactJ1L27_holds

end FrontierE3

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
