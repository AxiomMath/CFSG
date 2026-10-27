module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVLeviFacts
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutSp

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]


variable [Finite K] [CharP K 2]

theorem isAutConjIn_vLevi_highRootSL2 :
    E6Pilot.IsAutConjIn (vLevi K) ((EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)) := by
  rw [← map_vLeviEquiv_spRootSL2, ← Subgroup.map_map]
  exact (E6Pilot.isAutConj_spRootSL2 le_rfl _).isAutConjIn_map (vLeviEquiv K)

end CFSG.SeitzReduction.E7Pilot
