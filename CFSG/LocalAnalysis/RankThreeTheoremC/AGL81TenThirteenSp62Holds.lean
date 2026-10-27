module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenSp62Close
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.StrongThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Sp62FrameLocal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8FrameModel
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PLTypeHolds
public import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPL
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinVoid
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosLevi
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoVoid
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.NineThree
public import CFSG.HardMathSupport.Foote.Coordinator.Downstream
public import CFSG.CGT.PushingUpLit.TwoKHolds
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympMain
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusMain
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusPosLevi
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSmall
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSplit
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockReduceLevi
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaEightMinusAut
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62RankFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightFourProof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen


variable (G : Type) [Group G] [Finite G] in
theorem agl81TenThirteenSp62_holds
    : AGL81TenThirteenSp62 G := by
  have hTPL : CFSG.AGLEmbedding.CitedBlockTransvectionPL :=
    CFSG.AGLEmbedding.citedBlockTransvectionPL_of_type
      CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds
  have hGAS : CFSG.Open.GriessAllModelsStatement :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hZr : CFSG.AGLEmbedding.OddCenterRest := CFSG.AGLEmbedding.oddCenterRest_of_griess hGAS
  have hLevi : CFSG.AGLEmbedding.KFactBlockLeviU42 :=
    CFSG.AGLEmbedding.kFactBlockLeviU42_of hTPL CFSG.AGLEmbedding.citedBlockAltSevenPL_holds
      (CFSG.AGLEmbedding.kFactCompParabLeviU42_of_families
        (CFSG.AGLEmbedding.kFactCompParabLeviU42On_linear hGAS)
        CFSG.AGLEmbedding.kFactCompParabLeviU42On_twistedA
        (CFSG.AGLEmbedding.kFactCompParabLeviU42On_idxB hZr)
        (CFSG.AGLEmbedding.kFactCompParabLeviU42On_idxD hZr)
        (CFSG.AGLEmbedding.kFactCompParabLeviU42On_twistedD_all hZr)
        (CFSG.AGLEmbedding.kFactCompParabLeviU42On_g2 hGAS)
        CFSG.AGLEmbedding.kFactCompParabLeviU42_small)
  exact agl81TenThirteenSp62_of G KFactProofs.gl83StronglyEmbeddedThreeSolvable_holds
    kFactSp62CfgLocal_holds KFactProofs.kFactSp62Frame_holds KFactProofs.kFactOmega8Frame_holds
    hLevi CFSG.AGLEmbedding.kFactOmegaEightMinusAut kFactU62ThreeRank kFactOmegaMinusThreeRank
    (CFSG.AGLEmbedding.asc81bEightFour_of_cgtBlock aschbacherLocalCGTBlock_proved)
    (CFSG.AGLEmbedding.asc81bEightFive_of_factorization aschbacherLocalFactorization_proved)
    (CFSG.AGLEmbedding.asc81bEightSix_of_bhs bhsLocalCStar_proved)
    BlockB.asc81bNineThree_holds
    (d1NoXBlock3_of_inputsK CFSG.HardMathSupport.Foote.Coordinator.aschbacherTheoremOneK_proved
      CFSG.CGT.PushingUpLit.aschbacherTheoremTwoK_holds
      CFSG.CGT.PushingUpLit.solomonAlternatingBlockK_holds)
    Hyp111.agl81NineEightFour_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
