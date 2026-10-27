module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217SigmaDefs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Assembly
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTwelveOneSigmaStrong
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTwelveOneSigmaThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoRestThree
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217L34
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeEightFiveProof
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.AltSixCoreProof

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC

theorem o1217Sigma_of_gen (h : O1217SigmaGen) :
    CFSG.LocalAnalysis.RankThreeUC.S15.O1217Sigma := by
  intro G _ _ hS hUC M hM hwit hst
  have hC : CStarGen G :=
    CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.cStarGen_of_rankThreeUC hS hUC
  obtain ⟨p, hp, -⟩ := hwit
  have hσ : (sigmaSet G M).Nonempty :=
    ⟨p, by
      simpa [sigmaSet, CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hp⟩
  exact h G hC M hM hσ hst

section Cert


theorem o1217SigmaGen_holds
    : O1217SigmaGen :=
  o1217SigmaGen_of_inputs nineFourTwoSigmaGen_holds
    (nineTwelveOneSigmaStrong_holds
      CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds) nineTwelveOneSigmaThree_holds
    (CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.kFactNineThreeNoTwo_of_rest
      (CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.kFactNineThreeNoTwoRest_of_restTwo
        (CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.kFactNineThreeNoTwoRestTwo_of_restThree
          CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.kFactNineThreeNoTwoRestThree_holds)))
    kFactL34InvTwo_holds kFactThreeEightFive_holds
    kFactCentralLift_holds kFactAltSixCoreCentral_holds

theorem o1217Sigma_holds
    : CFSG.LocalAnalysis.RankThreeUC.S15.O1217Sigma :=
  o1217Sigma_of_gen o1217SigmaGen_holds

end Cert

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
