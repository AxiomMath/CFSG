module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.YSLeavesKData
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGAll
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicCoverLevi
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291A3Rest
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291L64Rest
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFSporB
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPLinUniMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFCo1
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharFinal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291G2RankMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieFinal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGTvMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcInputs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCMon13DHolds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoL3
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278ChevP
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactAutAlt
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2715
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPCase1
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278ChevQ
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278Spor
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDL64I204U3
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDL64I204L2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401ThreeMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401OmegaMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKG2024Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAStd
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiHolds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALangMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiOuterNPC
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGHolds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCHolds

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Yardstones.Md8ed6d263d89 (YSPEmptyPlaneLocals)

section YS08


theorem ysPEmptyPlaneLocals_holds : YSPEmptyPlaneLocals :=
  ysPEmptyPlaneLocals_of_l6leaves kd291LinUniZero_holds kd291LinUniModel_holds
    (kd292CaseALin_of_lang kd292LangConjInput_holds) kd292CaseAUni_holds kd292CaseBSylow_holds kd292CaseBConstr_holds
    (kd291a3_of_defChar (kd291DefCharL_of_g2Prime KD291DC.inG2Prime_holds))
    (kFactP65RankThree_of_kdata (kdL64I291_of_defChar_outerLie (kd291DefCharL_of_g2Prime
    KD291DC.inG2Prime_holds) (KD291OL.kd291OuterLie_of_cross KD291OL.outerFixedRankCross_holds))
    (kdL64I246_of_rest kdL64I246Rest_holds) kdL64TypeRank_holds kdL64I204L2_holds)
    (kFactP65RankTwo_of_kdata' kdI278ChevP_holds kdI278ChevQ_holds kdI278Spor_holds
    kdI278SporB_holds (kdI278SporC_of_monster Monster13.kdI278SporCMonster_holds) kdL64I204U3_holds)
    (kFact64iiNPC_of_outer kFact64iiOuterSylow_holds kFact64iiOuterNPC_holds)
    (stepKGroupCore_of_kfacts (kFact64iiL_of_outer kFact64iiOuterSylow_holds) (kd291a3_of_defChar
    (kd291DefCharL_of_g2Prime KD291DC.inG2Prime_holds)) (kFact613rankP_of_inputs
    (RankP.gl83I66Two_of_linUni RankP.gl83I66TwoLinUni_holds)) kFactAutAltOrder_holds
    kFactAutAltEmbed_holds kg2024_holds kFact2401Three_holds kFact2715_holds kFact131_holds
    (kFactParabolicCover_of_levi (kFactParabolicLevi_of_sub (KPLeviSub.kFactParabolicLeviSub_of_exc
    ParrottLeviExc.leviSubExcInputs_holds))) FongKGG.kgNoncycCent_holds kgTransvCent_holds
    kFact2401ThreeOmega_holds)

end YS08

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

end
