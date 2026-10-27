module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterHolds
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDetSix

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

section Open

theorem slmCatalogueClausesAt_of_open {m : ℕ} (hEO : CatSLmEvenOuterAt m)
    (hOdd : CatSLmOddLieAt m) (hSpor : CatSLmSporadicAt m) : SLmCatalogueClausesAt m :=
  ⟨catSLmAlternating, catSLmEvenInner, hEO, hOdd, hSpor, catSLmCovers⟩

end Open

section Inputs

theorem slmCatalogueClausesAt_of_inputs {m : ℕ} (hm : 3 ≤ m) (hdet : SLmEvenTypeDetAt m)
    (hGLS : GLS3OddLieAutComponentsInput) (hX : SLmNotOddLieInputAt m)
    (hSpor : CatSLmSporadicAt m) : SLmCatalogueClausesAt m :=
  slmCatalogueClausesAt_of_open (catSLmEvenOuterAt_of_typeDet hm hdet)
    (catSLmOddLieAt_of_inputs hGLS hm hX) hSpor

theorem slmCatalogueClausesAt_six (hGLS : GLS3OddLieAutComponentsInput)
    (hX : SLmNotOddLieInputAt 6) (hSpor : CatSLmSporadicAt 6) : SLmCatalogueClausesAt 6 :=
  slmCatalogueClausesAt_of_inputs (by norm_num) slmEvenTypeDetAt_six hGLS hX hSpor

end Inputs

end CFSG.SeitzReduction.LinearPilot
