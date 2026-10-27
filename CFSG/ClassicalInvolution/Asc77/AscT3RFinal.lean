module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIMain
public import CFSG.ClassicalInvolution.Asc77.AscT3R10aInv
public import CFSG.ClassicalInvolution.Asc77.AscT3R10bMain

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

variable (p f : ℕ) [Fact p.Prime]

theorem t3CaseII_of_residuals (hR3 : Res20_3 p f) (hR7 : Res20_7 p f) (hP1 : Res10bP1 p f)
    (hY : Res10aY p f) : T3CaseII p f :=
  t3CaseII_of_inputs_res hR3 hR7 (c20_9_of_rest (c20_9rest p f)) (c20_10a_of_Y p f hY)
    (c20_10b_of_P1 p f hP1)

end CFSG.ClassicalInvolution.Asc77.T3CII
