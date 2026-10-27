module

public import CFSG.ClassicalInvolution.Asc77.AscT7ASectC

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

theorem c21_2_final_sect (hE : ThmEWithSylow p f) (hHz : TwinFrameHyp51z p f)
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) (h1 : ThompsonCube p f)
    (h2 : ThompsonStar p f) (h3 : ThompsonClique p f) (h752 : L7_5_2 p f)
    (h5 : ThompsonGraph p f) (hMF : DStarConnectedTwin p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (h13N : C21_13_N p f)
    (h14N : C21_14_N p f) (h14a : C21_14_alt p f) (h15 : C21_15 p f) (hWyl : C21_WylTrans p f)
    (hY : C21_YSigma p f) : C21_2 p f := by
  have hC3 : C21_3 p f := c21_3_of p f (twinFrameHyp51_of_cases hHz hHt hHu)
  have h12 : C21_12 p f := c21_12_of_inputs p f h1 h2 h3 h752 h5
  exact c21_2_final' p f hE hHz hHt hHu h12 h13N
    (C21_13_wyl_of_star h12 (c21_13_star_of_sections p f hMF h3s hC3)) h14N h14a h15 hWyl hY
    (c21_17_tz_of_sections p f hMF h3s hC3) (c21_E_star_of_wylTrans p f hMF h3s hC3 hWyl)

end CFSG.ClassicalInvolution.Asc77
