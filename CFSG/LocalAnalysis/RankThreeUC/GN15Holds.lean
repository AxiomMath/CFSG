module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltRest
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltNatI532
public import CFSG.LocalAnalysis.RankThreeUC.GN15CoverHolds
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoHolds

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

set_option linter.unusedSectionVars false

open CFSG.HardMathSupport.Cooperstein.Coordinator (GF2EightFive)

theorem altEven_of_gf2EightFive (hGF : GF2EightFive) : GNInputRed.AltEven :=
  altEven_of_layer_and_baum (gnLayerHolds_of_gf2EightFive hGF) (gnBaumNormalizes_of_gf2EightFive hGF)

theorem altEven_holds : GNInputRed.AltEven :=
  altEven_of_gf2EightFive
    (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.gf2EightFive_of_b42L42Core
      CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.b42L42Core_holds)


theorem s15GNFactorShape_of_JOutCentral
    (hJ : JOutCentral) : S15GNFactorShape :=
  GNInputRed.factorShape_of_residuals (factor_of_JOutCentral hJ) GNInputRed.rankTwo_holds altEven_holds

theorem s15GNInput_of_JOutCentral
    (hJ : JOutCentral) : S15GNInput :=
  S15GNInput_of_factorShape (s15GNFactorShape_of_JOutCentral hJ)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

end
