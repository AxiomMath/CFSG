module

public import CFSG.GF2Type.AschbacherFSmith1977Holds
public import CFSG.GF2Type.Smith1979.CaseIHolds
public import CFSG.GF2Type.Smith1979.CaseIIHolds
public import CFSG.GF2Type.Smith1980Orth.Final

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

theorem widthSixAlternativeFourCase_of_inputs
    (h3 : CaseIIIStmt) (hAS : CFSG.Quasithin.H13.InputAS91) :
    CFSG.Yardstones.M3aba7dc4b8a8.WidthSixAlternativeFourCase :=
  widthSixAlternativeFourCase_of_core aschbacherFSmith1977Statement_holds
    Smith1980Orth.timInputs_holds.hDW Smith1980Orth.smith1980Orthogonal_holds hAS
    (widthSixCore_of_cases Smith1980Orth.timInputs_holds caseIStmt_holds caseIIStmt_holds h3)

end CFSG.GF2Type.Smith1979
