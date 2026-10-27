module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneToralB
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneToralCases

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

section Toral


set_option linter.unusedSectionVars false

theorem e6PlaneToral_proved : E6PlaneToralStmt := by
  intro K _ _ ω hω3 hω1 u huM hu3 hdim
  exact e6Toral_core hω3 hω1 (fun h3 h1 ρ σ hfr hrange h01 h12 hmono c w d n hw hcyc hsc =>
    e6Toral_caseB_bound h3 h1 hfr hrange h01 h12 hmono c w d n hw hcyc hsc) huM hu3 hdim

end Toral

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
