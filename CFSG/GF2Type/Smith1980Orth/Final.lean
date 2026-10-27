module

public import CFSG.GF2Type.Smith1980Orth.FullReduction
public import CFSG.LargeExtraspecial.AS62C36Main
public import CFSG.GF2Type.Smith1980Orth.TimGH74
public import CFSG.GF2Type.Smith1980Orth.TimGH74W4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14


theorem timInputs_holds : TimInputs :=
  timInputs_of_widthTwo aschbacherWidthTwoResidual_holds

theorem aschbacherSmithW4Input_holds : AschbacherSmithW4Input :=
  aschbacherSmithW4Input_of_widthTwo aschbacherWidthTwoResidual_holds

theorem smith1980OrthogonalSix_holds : Smith1980OrthogonalSixStatement :=
  smith1980OrthogonalSix_of_timInputs timInputs_holds
    (CFSG.Holt.H78.holtUniqueFixedPointSimple_of_holtTheorem1 CFSG.Holt.H78.holtTheorem1)
    identInput

theorem smith1980Orthogonal_holds : Smith1980OrthogonalStatement :=
  smith1980Orthogonal_of_timInputs timInputs_holds aschbacherSmithW4Input_holds

end CFSG.GF2Type.Smith1980Orth
