module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.D4
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4C3

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false

section Final


theorem y923_triD4_of_A2 (hA2 : TriD4Aux.TriD4A2NoL2) : Y923_TriD4 :=
  y923_triD4_of_residuals hA2 triD4C3NoL2_holds

theorem y923_d4_of_A2 (hA2 : TriD4Aux.TriD4A2NoL2) : Y923_D4 :=
  y923_d4_of_residuals hA2 triD4C3NoL2_holds

end Final

end CFSG.HardMathSupport.Dickson.Sec6.I923
