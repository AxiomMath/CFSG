module

public import CFSG.ClassicalInvolution.RouteD.G2D4T3Free
public import CFSG.ClassicalInvolution.Asc77.AscE18End

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic

variable {p : ℕ} [Fact p.Prime]

theorem thmEWithSylow_of_nonToral (f : ℕ) (hNT : G2D4Models.G2NonToralGenerate p) :
    ThmEWithSylow p f := by
  have h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n :=
    G2D4Models.h3s_of_nonToral_free hNT
  exact thmEWithSylow_of_steps p f
    (e18_9_of_rest f (e18_3 p f (l6_7_proved p f)) (e18_6_proved p f) (e18_7_proved p f h3s)
      (e18_4C p f (l6_9_proved p f) (l6_11_proved p f) h3s)
      G2D4Models.e189Rest_unconditional) h3s

end CFSG.ClassicalInvolution.Asc77
