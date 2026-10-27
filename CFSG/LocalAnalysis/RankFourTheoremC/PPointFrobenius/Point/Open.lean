module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.Final
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.SchurBound
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KE.Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionFinal
public import CFSG.LocalAnalysis.GL83PartI.I713.Final

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius


theorem ptKFacts_proved
    : PtKFacts :=
  ⟨CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction.kFactInnerAction_holds,
    GL83.I713.i_7_13_1_holds, KE.ke_holds⟩

theorem ysPPointCentralizers_proved
    : CFSG.Yardstones.Md8ed6d263d89.YSPPointCentralizers :=
  ysPPointCentralizers_of_kfacts ptKFacts_proved ptSchurBound_holds

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
