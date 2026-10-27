module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K64iiDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.SlotFrontier
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GlueThree
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614B1Main
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614B2Main
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614CEMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614FMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GMainThree
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HMainThree
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614JMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614DOGMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614DOLMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K278Main
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K64Main
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614KTrMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K3010Main
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Glue
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K135Main
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614KCRMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614KTwoMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Main
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614KBGMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IMainHolds
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GlueThree64
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614B2Three
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292Glue
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292SMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292TMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292LMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292UMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292NMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292XMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292CAMain
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292CBMain
import CFSG.LieType.ChevTwo.Reductions
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1CoreMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1RedMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.Lemma121
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionFinal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

section Assembly

theorem gl83I291Three_holds
    : T29.GL83I291Three :=
  T29.gl83I291Three_of_families (T29.noncyclicCentreRank_of_tables
      (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
      (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
          CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)) T29.altTripleCoverAbelianBound_holds
    T29.t29Spor_holds T29.t29Chev3_holds (T29.Parrott.t29ChevOther_of_kfacts
        T29.Parrott.t29LThreeEpsCase_holds T29.Parrott.outerFixedE9_holds
        T29.Parrott.innerFusionE9Exc_holds)

theorem slotP614Core_of_kFact64ii
    (k64ii : KFact64ii) : SlotP614Core :=
  slotP614Core_of_piecesThree pieceDelta4_holds pieceNotDelta_holds
    (pieceDeltaOmega_holds_of_l34 kFact278L34_holds kFactL34DiagGen_holds) pieceCoreTwo_holds
    pieceOmega_holds pieceCompSylow_holds pieceCompOmega_holds pieceChevAlt_holds
    piece619Three_holds piece620Three_holds piece620iii_holds pieceClosing_holds
    k64ii (kFact64iii_of_l34 kFact278L34_holds) kFactBenderGen_holds P614K136.kFactBenderTI_holds
    kFact135Three_holds (kFactTwoInvolutionsThree_of_rankOne kFactChevTwoRankOneThree_holds)
    kFactTransvRankOne_holds (kFact136Three_of_rankOne kFactChevTwoRankOneThree_holds)
    kFact3010_holds SmallRank.kFactSylowNormalizerIrreducible_holds
    (SmallRank.kFactOutThreePrimeSimple_of_innerAction Stroth.InnerAction.kFactInnerAction_holds) kFactZJFactorizationAny_holds
    kFactBlockFactorThreePrime_of_cgtBlock aschbacherLocalCGTBlock_proved
    (CFSG.LieType.ChevTwo.chev2KDOut_of_outTwoNilp CFSG.LieType.ChevTwo.chev2OutTwoNilp_of_leaves)
    (kFactCampbell_of_kFactCampbellBlock kFactCampbellBlock_holds) Lemma2813.kFactLemma2813_holds
    GL83.I_28_3_S3_proved (RankTwoUniq.kFactRankTwoUniqueness_of_core RankTwoUniq.k1Core_holds) kfactRankThreeStructure_proved
    gl83I291Three_holds (T29.noncyclicCentreRank_of_tables
        (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
        (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
            CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)) (kFactThreeComponentsQRank_of_catalog
        (T29.noncyclicCentreRank_of_tables
            (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
            (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
                CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds))
        (k3CatalogQCyc_of_lie
            (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
                CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
            (k3CatalogQCycLie_of_table
                (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement))))

theorem slotP614Core_of_kFact64iiThree
    (k64 : KFact64iiThree) : SlotP614Core :=
  slotP614Core_of_piecesThree64 pieceDelta4_holds pieceNotDeltaThree_holds
    (pieceDeltaOmega_holds_of_l34 kFact278L34_holds kFactL34DiagGen_holds) pieceCoreTwo_holds
    pieceOmega_holds pieceCompSylow_holds pieceCompOmegaThree_holds pieceChevAlt_holds
    piece619Three_holds piece620Three_holds piece620iii_holds pieceClosing_holds
    k64 (kFact64iii_of_l34 kFact278L34_holds) kFactBenderGen_holds P614K136.kFactBenderTI_holds
    kFact135Three_holds (kFactTwoInvolutionsThree_of_rankOne kFactChevTwoRankOneThree_holds)
    kFactTransvRankOne_holds (kFact136Three_of_rankOne kFactChevTwoRankOneThree_holds)
    kFact3010_holds SmallRank.kFactSylowNormalizerIrreducible_holds
    (SmallRank.kFactOutThreePrimeSimple_of_innerAction Stroth.InnerAction.kFactInnerAction_holds) kFactZJFactorizationAny_holds
    kFactBlockFactorThreePrime_of_cgtBlock aschbacherLocalCGTBlock_proved
    (CFSG.LieType.ChevTwo.chev2KDOut_of_outTwoNilp CFSG.LieType.ChevTwo.chev2OutTwoNilp_of_leaves)
    (kFactCampbell_of_kFactCampbellBlock kFactCampbellBlock_holds) Lemma2813.kFactLemma2813_holds
    GL83.I_28_3_S3_proved (RankTwoUniq.kFactRankTwoUniqueness_of_core RankTwoUniq.k1Core_holds) kfactRankThreeStructure_proved
    gl83I291Three_holds (T29.noncyclicCentreRank_of_tables
        (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
        (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
            CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)) (kFactThreeComponentsQRank_of_catalog
        (T29.noncyclicCentreRank_of_tables
            (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
            (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
                CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds))
        (k3CatalogQCyc_of_lie
            (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
                CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
            (k3CatalogQCycLie_of_table
                (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement))))

theorem slotP614CaseDelta_of_open
    (k292 : KFact292) : SlotP614CaseDelta :=
  slotP614CaseDelta_of_pieces pieceCaseDelta_holds k292 gl83I291Three_holds
    (T29.noncyclicCentreRank_of_tables
        (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
        (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
            CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)) (kFactThreeComponentsQRank_of_catalog
        (T29.noncyclicCentreRank_of_tables
            (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
            (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
                CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds))
        (k3CatalogQCyc_of_lie
            (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
                CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
            (k3CatalogQCycLie_of_table
                (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement))))

theorem kFact292_holds
    : KFact292 :=
  kFact292_of_pieces kD292Shape3_holds kD292TwoFrame3_holds kD292ThreeFrameLin3_holds
    kD292UniOuter3_holds kD292ThreeFrameNorm3_holds kD292FrameNormX3_holds kD292CaseA3_holds
    kD292CaseB3_holds gl83I291Three_holds

theorem slotP614CaseDelta_holds
    : SlotP614CaseDelta :=
  slotP614CaseDelta_of_open kFact292_holds

end Assembly

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
