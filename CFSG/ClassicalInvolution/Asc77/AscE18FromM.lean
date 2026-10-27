module

public import CFSG.ClassicalInvolution.Asc77.AscE18End
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedMain
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactMain
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8G2

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic

variable {p : ℕ} [Fact p.Prime]

theorem thmEWithSylow_of_maxNormalizer (f : ℕ) (hM : G2D4Models.G2D4MaxNormalizer p) :
    ThmEWithSylow p f := by
  have h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n := T3Typed.h3s_of_maxNormalizer hM
  exact thmEWithSylow_of_steps p f
    (e18_9_of_rest f (e18_3 p f (l6_7_proved p f)) (e18_6_proved p f) (e18_7_proved p f h3s)
      (e18_4C p f (l6_9_proved p f) (l6_11_proved p f) h3s)
      (G2D4Models.e189Rest_of_maxNormalizer hM)) h3s

theorem thmEWithSylow_of_split (f : ℕ) (hgen : T3Typed.G2CentralizersGenerate p)
    (hD4 : G2D4Models.TD4MaxNormalizer p) : ThmEWithSylow p f := by
  have h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n := T3Typed.h3s_of_split hgen hD4
  exact thmEWithSylow_of_steps p f
    (e18_9_of_rest f (e18_3 p f (l6_7_proved p f)) (e18_6_proved p f) (e18_7_proved p f h3s)
      (e18_4C p f (l6_9_proved p f) (l6_11_proved p f) h3s)
      (G2D4Models.e189Rest_of_td4MaxNormalizer hD4)) h3s

end CFSG.ClassicalInvolution.Asc77
