module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBInputs
public import CFSG.Milestones.CL_LIT_Aschbacher_component_type_theorem_5

public section

namespace CFSG.ComponentClassification.GSThmB

theorem aschbacherTheorem5Input_holds : AschbacherTheorem5Input :=
  fun G _ _ => Milestones.cl_lit_aschbacher_component_type_theorem_5 G

end CFSG.ComponentClassification.GSThmB
