module

public import CFSG.ClassicalInvolution.Asc77.AscT3WMain
public import CFSG.ClassicalInvolution.Asc77.AscT3UMain
public import CFSG.ClassicalInvolution.Asc77.AscT3VFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3W

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]


theorem t3CaseII_of_res10aY' (hY : Res10aY' p f) : T3CaseII p f :=
  t3CaseII_of_inputs_res (res20_3_of_hyp51At T3U.res20_7Hyp51At_proved)
    (res20_7_of_hyp51At T3U.res20_7Hyp51At_proved) (c20_9_of_rest (c20_9rest p f))
    (c20_10a_of_Y' p f hY) (c20_10b_of_P1 p f (res10bP1_proved p f))

theorem t3CaseII_of_parts (h1 : Res10aCyc p f) (h2 : Res10aFus p f) : T3CaseII p f :=
  t3CaseII_of_res10aY' (res10aY'_of_parts h1 h2)

end CFSG.ClassicalInvolution.Asc77.T3CII.T3W
