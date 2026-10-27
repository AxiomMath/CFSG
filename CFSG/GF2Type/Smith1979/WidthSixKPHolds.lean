module

public import CFSG.GF2Type.Smith1979.WidthSixKP
public import CFSG.GF2Type.Smith1979.CaseIHolds
public import CFSG.GF2Type.Smith1979.CaseIIHolds
public import CFSG.GF2Type.Smith1979.GammaU.CaseIIIProof
public import CFSG.GF2Type.Smith1980Orth.Final
public import CFSG.GF2Type.AschbacherFSmith1977Holds

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

theorem smith1979WidthSixCharTwoKP_of_inputAS91 (hAS : CFSG.Quasithin.H13.InputAS91) :
    Smith1979WidthSixCharTwoKP :=
  smith1979WidthSixCharTwoKP_of_core aschbacherFSmith1977Statement_holds
    Smith1980Orth.timInputs_holds.hDW Smith1980Orth.smith1980Orthogonal_holds hAS
    (widthSixCore_of_cases Smith1980Orth.timInputs_holds caseIStmt_holds caseIIStmt_holds
        GammaU.Dict.caseIIIStmt)

end CFSG.GF2Type.Smith1979
