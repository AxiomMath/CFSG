module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCGoldD
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCT5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

section Final


theorem a7TC_proved (hE : A7ThmE) (GS : Hat2A7.GoldschmidtStronglyClosedExponent) : A7TC :=
  a7TC_of_res hE (a7TCRes_of_thin_match a7TCThin_proved (a7TCMatch_of_gs GS))

end Final

end CFSG.ClassicalInvolution.Hat2A7S
