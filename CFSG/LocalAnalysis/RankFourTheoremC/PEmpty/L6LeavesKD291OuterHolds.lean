module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLin
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterUni
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

theorem kd291OuterLin_holds
    : KD291OuterLin :=
  kd291OuterLin_of_griess CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

theorem kd291OuterUni_holds
    : KD291OuterUni :=
  kd291OuterUni_of_griess CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
