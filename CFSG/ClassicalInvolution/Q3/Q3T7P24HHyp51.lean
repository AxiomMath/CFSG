module

public import CFSG.ClassicalInvolution.Q3.Q3T6DH51Twin
public import CFSG.ClassicalInvolution.Q3.Q3T7Layer
public import CFSG.ClassicalInvolution.Q3.Q3T7P24H01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

section Inner


theorem hyp51TwinInnerThree_proved : Hyp51TwinInnerThree := by
  intro G _ _ _ Ω K₀ hst K K' b d c hKΩ hK'Ω _ hbK hbK' hMK hMK' B hB hbB hdB hcB hBgen hc1 hbc
    hd1 hdb _ hdsup
  have hΩ : HypOmegaModT Ω := hst.modU
  have hcK : IsClassicalMember3 K b := (isClassicalMember_of_twin hΩ hKΩ hbK).toQ3 (by norm_num)
  have hcK' : IsClassicalMember3 K' b := (isClassicalMember_of_twin hΩ hK'Ω hbK').toQ3 (by norm_num)
  exact Q3T6D.hyp51At_of_twin_layer3_proved (Q3T7.inClass3_of_stand3 hst.toStand3)
    (Q3T7.cit3Below_of_stand3 hst.toStand3) (T7C.exists_not_commute_of_stand hst) hcK hcK' hbK hbK'
    hMK hMK' hB hbB hdB hcB hBgen hc1 hbc hd1 hdb hdsup

end Inner

end CFSG.ClassicalInvolution.Q3.Q3T7P24
