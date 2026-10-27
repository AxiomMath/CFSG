module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.YSLeavesKData
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDAssemble
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630PConstr
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630AltSixSub15
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630AutQ8D8Five
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Final
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630I2026Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxSLBridge
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxSLM11
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactReeL28
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicCoverLevi
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291A3Rest
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291L64Rest
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFSporB
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPLinUniMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFCo1
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharFinal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291G2RankMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoL3
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278ChevP
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutOdd
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactReeBorel
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2715
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401Spor
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactJ1L27
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2024
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPCase1
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieFinal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcInputs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCMon13DHolds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenHolds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelFinal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2025G2Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCHolds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMain5
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278ChevQ
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278Spor
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDL64I204U3
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDL64I204L2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401ThreeMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKG2024Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDDihedralTypeSylow
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019RootMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigRows7
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigRows8
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4Rows
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottSporUniqueRankCo2

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open FongSporLocal
open CFSG.Yardstones.Md8ed6d263d89 (YSPEmptyStrongOfPlaneLocals)

section CertificateInstances

theorem ysPEmptyStrongOfPlaneLocals_holds
    : YSPEmptyStrongOfPlaneLocals :=
  ysPEmptyStrongOfPlaneLocals_of_l6leaves kd309_holds (kd291a3_of_defChar (kd291DefCharL_of_g2Prime
    KD291DC.inG2Prime_holds)) (kFactP65RankThree_of_kdata (kdL64I291_of_defChar_outerLie
    (kd291DefCharL_of_g2Prime KD291DC.inG2Prime_holds) (KD291OL.kd291OuterLie_of_cross
    KD291OL.outerFixedRankCross_holds)) (kdL64I246_of_rest kdL64I246Rest_holds) kdL64TypeRank_holds
    kdL64I204L2_holds) (kFactP65RankTwo_of_kdata' kdI278ChevP_holds kdI278ChevQ_holds
    kdI278Spor_holds kdI278SporB_holds (kdI278SporC_of_monster Monster13.kdI278SporCMonster_holds)
    kdL64I204U3_holds)
    (L630.s62L630Iii_of_kfacts_full L630.kFactI2026_holds L630.kFactAutQ8D8Five_holds
      (L630.l613f3_of_inputs (kd291a3_of_defChar (kd291DefCharL_of_g2Prime
        KD291DC.inG2Prime_holds)))
      (L630.sigmaSixSectionFact_of_alt L630.kFactAltSixSub15_holds)
      L630.pConstrainedFivePart_holds)
    (L6KD.s622KFactD_of_kfacts kFactFieldAutEven_holds kFactFieldAutOdd_holds) (s622Kx_of_inputs'
    (l613_of_inputs (kd291a3_of_defChar (kd291DefCharL_of_g2Prime KD291DC.inG2Prime_holds))
    (kFact613rankP_of_inputs (RankP.gl83I66Two_of_linUni RankP.gl83I66TwoLinUni_holds)))
    (kFactDihedralTypeAut_of_sylow kdDihedralTypeSylow_holds) kFactReeL28_holds kFactReeBorel_holds
    (kFact2024_of_kg2024 kg2024_holds) kFact2401Three_holds kFact2314_holds kFact1019_holds
    (kFact2025_of_g2 kFact2025G2_holds) kFact131_holds kFactParabolicGen_holds kFact2715_holds
    (kFactParabolicCover_of_levi (kFactParabolicLevi_of_sub (KPLeviSub.kFactParabolicLeviSub_of_exc
    ParrottLeviExc.leviSubExcInputs_holds))) kFact2401Spor_holds kFactSporM11_holds kFactJ1L27_holds
    (FongSporLocal.kFactSporLocal_of_rows3 (openRows3_of_openRows4 (openRows4_of_openRows5
    ⟨row_J4_7, row_J4_31, row_J4_43, row_Co2_11, row_HN_11⟩))))

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
