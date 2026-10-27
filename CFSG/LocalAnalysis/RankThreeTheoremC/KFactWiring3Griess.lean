module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactWiring3Kf1
public import CFSG.RankThree.PartOne.K159.CenterRankGriess
public import CFSG.RankThree.PartOne.TCB.Final

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC


theorem kF1At_of_griess {G : Type} [Group G] [Finite G]
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) (hS : Setting G) :
    KF1At G :=
  kF1At_of_centerRankFour (CFSG.RankThree.PartOne.K159.centerRankFour_of_griess
    CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge hGA) hS

end CFSG.LocalAnalysis.RankThreeTheoremC
