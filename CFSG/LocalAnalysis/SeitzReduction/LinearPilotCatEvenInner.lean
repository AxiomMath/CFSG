module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatStatement
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenInner

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf

theorem catSLmEvenInner :
    CatSLmEvenInner := by
  intro S _ _ hS hna heven σ hσ hin m f D hD _
  have := hS
  exact F4Pilot.false_of_isComponent_fixedSubgroup_inner hna
    (involutionCentralizersComponentFree_of_evenLieType heven) hσ hin hD

end CFSG.SeitzReduction.LinearPilot
