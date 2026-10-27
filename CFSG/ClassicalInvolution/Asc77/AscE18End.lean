module

public import CFSG.ClassicalInvolution.Asc77.AscE18Wire
public import CFSG.StronglyEmbedded.UniqueCosetE18

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

theorem e18_endS : E18_endS p f := CFSG.StronglyEmbedded.UniqueCoset.e18_endC p f

theorem minCexFalse_of_e18_9 (h9 : E18_9 p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) : MinCexFalse p f :=
  minCexFalse_of_steps' p f (e18_6_proved p f) (e18_8z_proved p f h3s) h9 (e18_endS p f)

theorem thmEWithSylow_of_steps (h9 : E18_9 p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) : ThmEWithSylow p f :=
  thmEWithSylow_of_minCexFalse p f (minCexFalse_of_e18_9 p f h9 h3s)

end CFSG.ClassicalInvolution.Asc77
