module

public import CFSG.GF2Type.Smith1979.WidthSixInputs
public import CFSG.GF2Type.Smith1979.GammaU.CaseIIIProof

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

theorem widthSixAlternativeFourCase_of_parrott (hAS : CFSG.Quasithin.H13.InputAS91) :
    CFSG.Yardstones.M3aba7dc4b8a8.WidthSixAlternativeFourCase :=
  widthSixAlternativeFourCase_of_inputs GammaU.Dict.caseIIIStmt hAS

end CFSG.GF2Type.Smith1979
