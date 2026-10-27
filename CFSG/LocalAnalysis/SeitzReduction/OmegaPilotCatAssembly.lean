module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatEvenOuterHolds
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatOdd

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

theorem omegaCatalogueClausesAt_of_open {m : ℕ} (hOdd : CatOmegaOddLieAt m)
    (hSpor : CatOmegaSporadicAt m) : OmegaCatalogueClausesAt m :=
  ⟨catOmegaAlternating, catOmegaEvenInner, catOmegaEvenOuterAt m, hOdd, hSpor, catOmegaCovers⟩

theorem omegaCatalogueClausesAt_of_inputs {m : ℕ} (hGLS : GLS3OddLieAutComponentsInput)
    (hX : OmegaNotOddLieInputAt m) (hSpor : CatOmegaSporadicAt m) : OmegaCatalogueClausesAt m :=
  omegaCatalogueClausesAt_of_open (catOmegaOddLieAt_of_inputs hGLS hX) hSpor

end CFSG.SeitzReduction.OmegaPilot
