module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcChar3
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Char3Untw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Char3D4

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md42047359a2a

set_option linter.unusedSectionVars false


theorem excChar3OuterExport_holds : ExcChar3OuterExport := by
  intro S _ _ hs hna idx hF h3 he β hβ hout
  by_cases hT : ∃ q, idx.1 = .trialityD4 q
  · exact lieCompExport_char3_outer_of_trialityD4_idx S hs hna idx hT h3 he β hβ hout
  · push Not at hT
    exact Or.inl (lieCompExport_char3_outer_of_ne_trialityD4 S hs hna idx hF hT h3 he β hβ hout)

theorem d4OuterExport_holds (hodd : TrialityOddA2Comps) : D4OuterExport :=
  d4OuterExport_of hodd d4Char3Outer_holds

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
