module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerLinearFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerUnitaryFinal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

theorem almostSimpleTowerResidual_holds : AlmostSimpleTowerResidual :=
  ⟨linearOuterResidual_holds, unitaryOuterResidual_holds⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
