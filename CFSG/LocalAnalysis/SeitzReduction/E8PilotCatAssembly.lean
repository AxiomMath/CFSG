module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatEvenExc

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

theorem e7CatalogueClauses_of_open (hOdd : CatE7OddLie) (hSpor : CatE7Sporadic) :
    E7CatalogueClauses :=
  ⟨catE7Alternating, catE7EvenInner, catE7EvenOuter, hOdd, hSpor, catE7Covers⟩

theorem e7CatalogueClauses_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hX : E7NotOddLieInput) (hSpor : CatE7Sporadic) : E7CatalogueClauses :=
  e7CatalogueClauses_of_open (catE7OddLie_of_inputs hGLS hX) hSpor

end CFSG.SeitzReduction.E8Pilot
