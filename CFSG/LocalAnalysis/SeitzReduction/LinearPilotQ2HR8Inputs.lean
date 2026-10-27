module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAssembly
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

theorem slmCatalogueClausesAt_of_gls3_sporadic {m : ℕ} (hm : 3 ≤ m)
    (hGLS : GLS3OddLieAutComponentsInput) (hSpor : CatSLmSporadicAt m) :
    SLmCatalogueClausesAt m :=
  slmCatalogueClausesAt_of_inputs hm (slmEvenTypeDetAt hm) hGLS
    (CrossChar.sLmNotOddLieInputAt (by omega)) hSpor

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

end CFSG.SeitzReduction.LinearPilot
