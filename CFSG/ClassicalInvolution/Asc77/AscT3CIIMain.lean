module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIOmegaMain
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC3
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC5
public import CFSG.ClassicalInvolution.Asc77.AscT3CLate8

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

variable {p f : ℕ} [Fact p.Prime]

theorem t3CaseII_of_inputs_hex (hex : HexAll p f) (h3 : C20_3 p f) (h5 : C20_5 p f)
    (h8 : C20_8 p f) (h9 : C20_9 p f) (h10a : C20_10a p f) (h10b : C20_10b p f) :
    T3CaseII p f :=
  t3CaseII_of_steps sec20Setup_proved h3 (c20_4 hex) h5 (c20_7 p f) h8 h9 h10a h10b

theorem t3CaseII_of_inputs (h3 : C20_3 p f) (h5 : C20_5 p f) (h9 : C20_9 p f)
    (h10a : C20_10a p f) (h10b : C20_10b p f) : T3CaseII p f :=
  t3CaseII_of_inputs_hex (hexAll p f) h3 h5 (c20_8 p f) h9 h10a h10b

theorem t3CaseII_of_inputs_res (hres : Res20_3 p f) (h7 : Res20_7 p f) (h9 : C20_9 p f)
    (h10a : C20_10a p f) (h10b : C20_10b p f) : T3CaseII p f :=
  t3CaseII_of_inputs (c20_3_of_res hres) (c20_5_of_res20_7 h7) h9 h10a h10b

end CFSG.ClassicalInvolution.Asc77.T3CII
