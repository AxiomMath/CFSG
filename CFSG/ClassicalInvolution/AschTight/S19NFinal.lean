module

public import CFSG.ClassicalInvolution.AschTight.S19NThm6
public import CFSG.ClassicalInvolution.AschTight.S19TFinal

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19N

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

theorem thm6A_proved : Asc77.Thm6A p f :=
  thm6A_of_c19_11b' p f (S19T.c19_11b_proved p f)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19N
