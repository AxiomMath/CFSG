module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectF
public import CFSG.ClassicalInvolution.Asc77.AscE18FromNT
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinZ

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

theorem c21_2_final_H (hNT : G2D4Models.G2NonToralGenerate p) (hHt : TwinFrameHyp51t p f)
    (hHu : TwinFrameHyp51u p f) (hD4 : Ih8D4Star p f) (h13N : C21_13_N p f)
    (h14N : C21_14_N p f) (h14a : C21_14_alt p f) (h15 : C21_15 p f)
    (hWyl : C21_WylTrans' p f) : C21_2 p f :=
  c21_2_final_reduced_D4 p f (thmEWithSylow_of_nonToral f hNT) (twinFrameHyp51z p f) hHt hHu hD4
    (G2D4Models.h3s_of_nonToral_free hNT) h13N h14N h14a h15 hWyl

end CFSG.ClassicalInvolution.Asc77
