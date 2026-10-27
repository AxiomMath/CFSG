module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Open (ordD ordTwistedD)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (MonsterInnerInput MonsterLocalComponentsInput
  isComponent_map_mulEquiv mulAut_conj_injective_of_simple)

theorem evenLieOrder_POmega_six_one {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) :
    F4Pilot.evenLieOrder t 6 1 = 50027557148216524800 ∨
      F4Pilot.evenLieOrder t 6 1 = 51615733565620224000 := by
  rcases ht with rfl | rfl
  · left; decide
  · right; decide

end CFSG.SeitzReduction.OmegaPilot
