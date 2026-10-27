module

public import CFSG.ClassicalInvolution.Q3.Q3T8AF05
public import CFSG.ClassicalInvolution.Q3.Q3T8AFZ03
public import CFSG.ClassicalInvolution.Q3.Q3T8NFinal

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

section AlphaFrame


theorem alphaFrame3_of_zFacts (hZ : ZLinkFacts3) : AlphaFrame3 :=
  alphaFrame3_of_pure (pureLinkConst3_of_zFacts hZ)

theorem alphaFrame3_proved : AlphaFrame3 := alphaFrame3_of_zFacts zLinkFacts3_proved

end AlphaFrame

section Thm8


theorem thm8A3_of_c26_13 (h13 : C26_13) : Q3.Disc3.Thm8A3 :=
  thm8A3_of_inputs h13 alphaFrame3_proved

end Thm8

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
