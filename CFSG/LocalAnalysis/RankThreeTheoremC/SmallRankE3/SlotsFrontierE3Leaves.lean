module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.SlotsFrontierE3
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncycE3Frontier
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGL34Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291L64Rest
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDL64I204L2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicCoverLevi
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFCo1
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019RootMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactReeL28
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDDihedralTypeSylow
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291G2RankMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharFinal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviHolds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcInputs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMain3
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenHolds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2025G2Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCDispatch
public import CFSG.Yardstones.Mdac756b924db.Definitions

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section FrontierLeaves

theorem kFactP65RankThree_of_cross
    (hC : ∀ t, KD291OL.OuterFixedRankCrossAt t) :
    KFactP65RankThree :=
  kFactP65RankThree_of_kdata
    (kdL64I291_of_defChar_outerLie (kd291DefCharL_of_g2Prime KD291DC.inG2Prime_holds) (KD291OL.kd291OuterLie_of_cross hC))
    kdL64I246_holds kdL64TypeRank_holds kdL64I204L2_holds

theorem kFactP65RankThree_of_twisted
    (h2E6 : KD291OL.OuterFixedRankCrossAt .twistedE6)
    (h3D4 : KD291OL.OuterFixedRankCrossAt .trialityD4)
    (h2G2 : KD291OL.OuterFixedRankCrossAt .twistedG2)
    (h2F4 : KD291OL.OuterFixedRankCrossAt .twistedF4) : KFactP65RankThree :=
  kFactP65RankThree_of_cross (KD291OL.outerFixedRankCross_holds_of_twisted h2E6 h3D4 h2G2 h2F4)

theorem kFactParabolicCover_of_exc
    (h : KPLeviSub.LeviSubExcInputs) : KFactParabolicCover :=
  kFactParabolicCover_of_levi (kFactParabolicLevi_of_sub (KPLeviSub.kFactParabolicLeviSub_of_exc h))

theorem kFactDihedralTypeAut_viaSylow
    : KFactDihedralTypeAut :=
  kFactDihedralTypeAut_of_sylow kdDihedralTypeSylow_holds

theorem gl83SmallRankInterfaceE3_of_leaves
    (h2E6 : KD291OL.OuterFixedRankCrossAt .twistedE6)
    (h3D4 : KD291OL.OuterFixedRankCrossAt .trialityD4)
    (h2G2 : KD291OL.OuterFixedRankCrossAt .twistedG2)
    (h2F4 : KD291OL.OuterFixedRankCrossAt .twistedF4) :
    CFSG.Yardstones.Mdac756b924db.GL83SmallRankInterfaceE3 :=
  gl83SmallRankInterfaceE3_of_frontierE3_L34 (kFactP65RankThree_of_twisted h2E6 h3D4 h2G2 h2F4)
    FongLevi.kFactGammaLeviE3_holds
    (kFactParabolicCover_of_exc ParrottLeviExc.leviSubExcInputs_holds) kGNoncycCentL34_holds

theorem gl83SmallRankLemma630E3_of_leaves
    (h2E6 : KD291OL.OuterFixedRankCrossAt .twistedE6)
    (h3D4 : KD291OL.OuterFixedRankCrossAt .trialityD4)
    (h2G2 : KD291OL.OuterFixedRankCrossAt .twistedG2)
    (h2F4 : KD291OL.OuterFixedRankCrossAt .twistedF4) :
    CFSG.Yardstones.Mdac756b924db.GL83SmallRankLemma630E3 :=
  gl83SmallRankLemma630E3_of_frontierE3_L34 (kFactP65RankThree_of_twisted h2E6 h3D4 h2G2 h2F4)
    FongLevi.kFactGammaLeviE3_holds
    (kFactParabolicCover_of_exc ParrottLeviExc.leviSubExcInputs_holds) kGNoncycCentL34_holds

theorem gl83SmallRankProp622E3_of_leaves
    (h2E6 : KD291OL.OuterFixedRankCrossAt .twistedE6)
    (h3D4 : KD291OL.OuterFixedRankCrossAt .trialityD4)
    (h2G2 : KD291OL.OuterFixedRankCrossAt .twistedG2)
    (h2F4 : KD291OL.OuterFixedRankCrossAt .twistedF4)
    (hrows : FongSporLocal.OpenRows3) :
    CFSG.Yardstones.Mdac756b924db.GL83SmallRankProp622E3 :=
  gl83SmallRankProp622_of_frontierE3 (kFactP65RankThree_of_twisted h2E6 h3D4 h2G2 h2F4)
    (slotP614CoreLargeU0_of_frontierE3_L34 (kFactP65RankThree_of_twisted h2E6 h3D4 h2G2 h2F4)
      FongLevi.kFactGammaLeviE3_holds
      (kFactParabolicCover_of_exc ParrottLeviExc.leviSubExcInputs_holds) kGNoncycCentL34_holds)
    kFactFieldAutEven_holds kFactDihedralTypeAut_viaSylow kFactReeL28_holds kFact1019_holds kFact2025_holds
    kFactParabolicGen_holds (kFactParabolicCover_of_exc ParrottLeviExc.leviSubExcInputs_holds)
    (FongSporLocal.kFactSporLocal_of_rows3 hrows)

end FrontierLeaves

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
