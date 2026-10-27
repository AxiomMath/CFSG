module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAssembly
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34ONOuterAssembly
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint

theorem slmCatalogueClausesAt_three_G2 : SeitzReduction.LinearPilot.SLmCatalogueClausesAt 3 :=
  SeitzReduction.LinearPilot.slmCatalogueClausesAt_of_inputs le_rfl
    (SeitzReduction.LinearPilot.slmEvenTypeDetAt le_rfl)
    SeitzReduction.gls3OddLieAutComponentsInput
    (SeitzReduction.CrossChar.sLmNotOddLieInputAt (by norm_num))
    SeitzReduction.LinearPilot.catSLmSporadicAt_three

end CFSG.LocalAnalysis.EvenBN.G2
