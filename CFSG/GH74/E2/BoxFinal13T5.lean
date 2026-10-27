module

public import CFSG.GH74.E2.BoxFinal13
public import CFSG.Milestones.CL_LIT_Aschbacher_component_type_theorem_5

public section

namespace CFSG.GH74.E2

open CFSG.GH74.Generic

theorem Box.aschbacherTheorem5
    : Box.AschbacherTheorem5Statement :=
  CFSG.Milestones.cl_lit_aschbacher_component_type_theorem_5

theorem s_restrictedEvenThin_final13'
    (hGKF : GenericKnownFacts) (hAS : AschbacherStandardL33)
    (hASM : AschbacherStandardM11) : S_restrictedEvenThin :=
  s_restrictedEvenThin_final13 hGKF Box.aschbacherTheorem5 hAS hASM

end CFSG.GH74.E2
