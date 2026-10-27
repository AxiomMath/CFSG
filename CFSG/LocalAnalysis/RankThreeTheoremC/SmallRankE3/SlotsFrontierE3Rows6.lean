module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.SlotsFrontierE3Leaves
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMain6
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCHolds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

theorem gl83SmallRankProp622E3_of_rows6
    (hrows : FongSporLocal.OpenRows6) :
    CFSG.Yardstones.Mdac756b924db.GL83SmallRankProp622E3 :=
  gl83SmallRankProp622E3_of_leaves (KD291OL.outerFixedRankCross_holds _)
    (KD291OL.outerFixedRankCross_holds _) (KD291OL.outerFixedRankCross_holds _)
    (KD291OL.outerFixedRankCross_holds _)
    (FongSporLocal.openRows3_of_openRows4 (FongSporLocal.openRows4_of_openRows5
      (FongSporLocal.openRows5_of_openRows6 hrows)))

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
