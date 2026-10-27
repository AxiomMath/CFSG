module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21Final
public import CFSG.ClassicalInvolution.Q3.Q3T7W21Hz
public import CFSG.ClassicalInvolution.Q3.Q3T7W21Zt

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7W21

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3T7
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77


theorem c21_2Three_of_residuals (hE : Q3T7E.ThmEWithSylow3) (hHt : TwinFrameHyp51t)
    (hHu : TwinFrameHyp51u) (hZT : C21_14_ZT) (hN : C21_NormCent) : C21_2Three := by
  have hHz : TwinFrameHyp51z := twinFrameHyp51z_proved
  have hMF : DStarConnectedTwinGen := dstarConnectedTwinGen_of
  have h3s : ∀ n, Q3T8.Generic.CITBelowU n → T3.Thm3SectBelow n :=
    fun _ h => Q3T7E.thm3SectBelow3_of_ih h
  have hC3 : C21_3 := c21_3_of (twinFrameHyp51_of_cases hHz hHt hHu)
  have hM : C21_13_M_ne := c21_13_M_ne_of_c21_3 hC3
  have hY : C21_14_Y_disc := c21_14_Y_disc_of_zt hC3 hZT
  exact c21_2Three_of_claims hE hHz hHt hHu c21_12_proved (c21_13_star_of_sections_gen hMF h3s hC3)
    (c21_17_tz_of_sections_gen hMF h3s hC3)
    (c21_E_star_of_starCent hMF h3s hC3 c21_starCent_proved)
    (c21_13_N_of_ne hMF h3s hC3 (c21_13_N_ne_of_M hMF h3s hC3 hM))
    (c21_14_N_of_rest hC3 (c21_14_N_rest_of hC3 hM (c21_14_N_disc_of_Ydisc hC3 hY)))
    (c21_14_alt_of_rest (c21_14_alt_rest_of hC3 hY hN)) (c21_15_of_normCent hC3 hN)
    (c21_YSigma_of_sections h3s)

end CFSG.ClassicalInvolution.Q3.Q3T7W21
