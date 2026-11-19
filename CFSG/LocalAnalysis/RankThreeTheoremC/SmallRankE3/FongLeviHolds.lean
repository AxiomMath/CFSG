module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviRank1
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviBBig
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviG2Field
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviTri
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviRee
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviABig
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviTABig
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviB3
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviD4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open TauCeti Subgroup CFSG.Open

section

set_option linter.unusedSectionVars false


theorem kFactGammaLeviE3_holds :
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KFactGammaLeviE3 :=
  kFactGammaLeviE3_of_inputs
    { a1 := @fun _A _ _ _K _K₀ _B _z _p S _q hq2 hv e =>
        a1_false S hq2 hv e
      a3 := @fun _A _ _ _K _K₀ _B _z _p S _q hq2 hv e =>
        a3_e3_full S hq2 hv e
      aBig := @fun _A _ _ _K _K₀ _B _z _p S _n hn _q hq2 hodd hv e =>
        aBig_false S hn hq2 hodd hv e
      tA2 := @fun _A _ _ _K _K₀ _B _z _p S _q hq2 hv e =>
        tA2_false S hq2 hv e
      tABig := @fun _A _ _ _K _K₀ _B _z _p S _n hn _q hq2 hv e =>
        tABig_false S hn hq2 hv e
      b2 := @fun _A _ _ _K _K₀ _B _z _p S _q hq2 hv e =>
        b2_false S hq2 hv e
      b3 := @fun _A _ _ _K _K₀ _B _z _p S _q hq2 hv e =>
        b3_e3_full S hq2 hv e
      bBig := @fun _A _ _ _K _K₀ _B _z _p S _n hn _q hq2 hv e =>
        bBig_false S hn hq2 hv e
      tD4 := @fun _A _ _ _K _K₀ _B _z _p S _q hq2 hv e =>
        tD4_e3_full S hq2 hv e
      g2 := @fun _A _ _ _K _K₀ _B _z _p S _q hq2 hv e =>
        g2_false S hq2 hv e
      tri := @fun _A _ _ _K _K₀ _B _z _p S _q hq2 hv e =>
        tri_false S hq2 hv e
      suz := @fun _A _ _ _K _K₀ _B _z _p S _m hv e =>
        suz_false S hv e
      ree := @fun _A _ _ _K _K₀ _B _z _p S _m hv e =>
        ree_false S hv e
      tits := @fun _A _ _ _K _K₀ _B _z _p S hv e =>
        tits_false S hv e
      alt := @fun _A _ _ _K _K₀ _B _z _p S _n hn h e =>
        alt_false S hn h e
      a1seven := @fun _A _ _ _K _K₀ _B _z _p S _q hq hv e =>
        a1seven_false S hq hv e
      tA2three := @fun _A _ _ _K _K₀ _B _z _p S _q hq hv e =>
        tA2three_false S hq hv e }

end

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
