module

public import CFSG.ClassicalInvolution.Asc77.AscT7AStep14
public import CFSG.ClassicalInvolution.Asc77.AscT7AAlphaTwin

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

theorem c21_4_final (hH51 : TwinFrameHyp51 p f) : C21_4 p f :=
  c21_4_of (c21_3_of p f hH51) (twinNormAlpha_of p f (c21_3_of p f hH51))

theorem c21_2_final (hE : ThmEWithSylow p f) (hHz : TwinFrameHyp51z p f)
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) (h12 : C21_12 p f)
    (h13 : C21_13 p f) (h14 : C21_14 p f) (h15 : C21_15 p f) (hWyl : C21_WylTrans p f)
    (hY : C21_YSigma p f) (h17t : C21_17_tz p f) (hEs : C21_E_star p f) : C21_2 p f :=
  c21_2_of_inputs p f hE hHz hHt hHu
    (twinNormAlpha_of p f (c21_3_of p f (twinFrameHyp51_of_cases hHz hHt hHu))) h12 h13 h14 h15
    hWyl (c21_17_cent_of p f h14 hY h17t) (c21_E_cent_of p f h14 hY hEs)

end CFSG.ClassicalInvolution.Asc77
