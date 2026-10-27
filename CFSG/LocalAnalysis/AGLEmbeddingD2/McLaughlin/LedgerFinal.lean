module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LowRankDerived
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.CitedSmallProofs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.Omega8Borel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LowRankNineThreeTwoProved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NineThreeSixEightEmpty
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.Omega8Lines
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.Omega8L32
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.NineThreeTwoResidueProof
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.U33ThreePrime
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5AtlasProved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Agl418
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentrePSU
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentreBlockPSU
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieFinal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverDoubling
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.NineThreeThreeTPLT
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PLTypeHolds
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.AutomizerMain
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NineThreeThreeFive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneProved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.Omega8Triality
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.E9Main
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Main
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.CitedFiveBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyL3Proved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddProved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankOneFinal
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Final
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Smith
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CatalogSchreier
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.Final
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Omega8Assembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OddTwoImages
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRKill3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OneImageOdd

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem d2PairStrongThree_of_citedInputs
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hGLSPlus : CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3StronglyThreeEmbeddedPlus)
    (hGN : GlaubermanNilesInput)
    (hFTR : FiveThreeAlt.AGL81FiveThreeRest) :
    D2PairStrongThree := by
  have hCF : CitedFive := citedFive_of_fiveThreeAlt (FiveThreeAlt.agl81FiveThreeAlt_of_rest hFTR)
  have hGF85 : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.gf2EightFive_of_b42L42Core
      CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.b42L42Core_holds
  have hSch : CFSG.AGLEmbedding.CatalogOuterSolvable := fun S _ _ _ hnab hcat =>
    CFSG.AGLEmbedding.kFactCatalogSchreier S ‹_› hnab hcat
  have hOdd : KFactLThreeTwoOddIndex := OddIndex.kFactLThreeTwoOddIndex_of_L3U3 hSch
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.kFactThreeRankOneSimple
    OddIndex.overgroupL32L3_proved
    (OddIndex.overgroupL32U3_of_U3Odd OddIndex.overgroupL32U3Odd_proved)
  have hK5 : KFactNineThreeThreeFive := kFactNineThreeThreeFive_proved
  have hCovO : KFactParabolicCoverOne := TightPairAndPureRank.kFactParabolicCoverOne_proved
  have hGLS : CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3StronglyThreeEmbedded :=
    CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.gls3_of_plus hGLSPlus
  have hAut : KFactStrongThreeAutomizer :=
    CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.kFactStrongThreeAutomizer_of_gls3Plus hGLSPlus
  have hTPLT : CitedBlockTransvectionPLType :=
    CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds
  have hΛ : KFactBlockInvertedThree := kFactBlockInvertedThree_holds h93 hTPLT
  have hK32 : KFactNineThreeThreeTwo := kFactNineThreeThreeTwo_of_tplt hTPLT
  have hPar : KFactOmega8Parabolic :=
    kFactOmega8Parabolic_of_parts kFactOmega8ParabolicL32_proved kFactOmega8ParabolicLines_proved
  have hPL : KFactBlockPLSylow := kFactBlockPLSylow_of_formalized
  have hCov8 : KFactParabolicCoverOmega8 := kFactParabolicCoverOmega8_proved
  have hLF : LargeFieldParabolic := largeFieldParabolic_proved
  have hK1 : KFactLowRankNineThreeTwo := kFactLowRankNineThreeTwo_proved
  have hKcN : KFactBlockCentreNine := OrdinaryProofs.kFactBlockCentreNine_proved
  have hKc : KFactBlockCentrePLRank := kFactBlockCentrePLRank_of_parts hKcN
    (kFactBlockCentreRankTwo_proved
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
  have hKc2 : KFactCentreBlockPLRank :=
    kFactCentreBlockPLRank_proved CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hU : OutU33 := outU33_proved
  have hL5 : OutL5 := OrdinaryProofs.outL5_proved
  have h418 : Agl418 := TightPairAndPureRank.agl418_proved
  have hSix : KFactBlockSixLie :=
    kFactBlockSixLie_of_noSwap CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
      (kFactBlockSixLieNoSwap_proved
        CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
  have hCovD : KFactParabolicCoverDoubling := TightPairAndPureRank.kFactParabolicCoverDoubling_proved
  have hTri : KFactOmega8Triality := Lie.kFactOmega8Triality_proved
  have hE9 : KFactParabolicE9NotTransitive :=
    kFactParabolicE9NotTransitive_proved
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hK : KFactStrongThreeSolv :=
    HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.kFactStrongThreeSolv_of_gls3
        CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds hGLS
  have hO27 : OutL27 := OrdinaryProofs.outL27_proved
  have hU33x : U33FactsExact := u33FactsExact_proved
  have hat : U33Atlas := u33Atlas_proved
  have hL5At : L5Atlas := l5Atlas_proved
  have hK2 : KFactOrthogonalTwoLieRank := kFactOrthogonalTwoLieRank_proved
  have hBor : KFactOmega8Borel := OrdinaryProofs.kFactOmega8Borel_proved
  have hL27 : L2SevenRankOne := l2SevenRankOne_proved
  have hJ : JordanPrimeCycle := jordanPrimeCycle_proved
  have hU33 : U33Facts := u33Facts_of_exact hU33x
  have hSA : SmallRankAtlas := smallRankAtlas_of_exact hU33x
  have hOm : PairOmega8S6Residue :=
    pairOmega8S6Residue_of_cited h93 hD2 hΛ hAut kFactOmega8Out_proved hTri hPar hGN hCov8 hK
      hBor hOdd
  have hcen1 : OneImageCentreResidue := oneImageCentreResidue_of_cited h93 hD2 hΛ hKc hKc2
  have hcen : PairBlockCentreThree := pairBlockCentreThree_of_cited h93 hD2 hKc
  have hK3 : KFactNineThreeThreeBig := kFactNineThreeThreeBig_of_two hK32
  have hLie : PairOneImageLieTR := pairOneImageLieTR_of_cited hD2 hLF hGN hCovO hK hSA
  have hres : LieOneImageResidue := lieOneImageResidue_of_omega h93 hD2 hΛ hAut hSix hOm
  have hlow : OneImageLowRankResidue :=
    oneImageLowRankResidue_of_clauseO hLF h418 hL27 h93 hD2 hΛ hU hL5 hO27 hK1 hK2
  have hO5 : OddOneImageKill :=
    oddOneImageKill_of_cited hLF h418 hL27 h93 hD2 hΛ hU hL5 hJ hGF85 hK3 hAut hE9 hcen
  exact d2PairStrongThree_of_two_images h93 hD2 hΛ
    (pairOddIndexResidue_of h93 hD2 hΛ hAut hcen oddTwoImageKill_proved hO5)
    (pairOneImagePureE_of_census hLF h418 hL27 h93 hD2 hΛ hU hL5 hJ hGF85 hLie hK3 hres hlow hcen1)
    (pairOneImageFixE_of_census hLF h418 hL27 h93 hD2 hΛ hU hL5 hJ hGF85 hLie hK3 hres hlow hcen1)
    hcen hLF h418 hL27 hGN hCovD hK rankImageOne_proved hCF hat hU33 hJ hGF85
    OrdinaryProofs.l32Atlas_proved hSA hK3
    (twoImageLowRankKill_of_cited hLF h418 hL27 h93 hD2 hΛ hU hL5 hO27 hK1 hK2)
    (pairTwoBadShape2Residue_of_cited h93 hD2 hΛ hPL hK2 hK32 hK5 h418 hL5At)

end CFSG.AGLEmbeddingD2.McLaughlin
