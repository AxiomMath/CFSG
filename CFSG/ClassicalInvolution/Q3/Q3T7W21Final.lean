module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21A03
public import CFSG.ClassicalInvolution.Q3.Q3T7P25Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7W21

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3T7
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77


theorem c21_2Three_of_claims (hE : Q3T7E.ThmEWithSylow3) (hHz : TwinFrameHyp51z)
    (hHt : TwinFrameHyp51t) (hHu : TwinFrameHyp51u) (h12 : C21_12) (h13s : C21_13_star)
    (h17tz : C21_17_tz) (hEstar : C21_E_star) (h13N : C21_13_N) (h14N : C21_14_N)
    (h14a : C21_14_alt) (h15 : C21_15) (hY : C21_YSigma) : C21_2Three := by
  intro G _ _ _ Ω K K' z hs
  exact c21_2_final_sect'' hE hHz hHt hHu h12 h13s h17tz hEstar h13N h14N h14a h15 hY G Ω K K' z
    (Q3T7P25.std7_of_three hs)

end CFSG.ClassicalInvolution.Q3.Q3T7W21
