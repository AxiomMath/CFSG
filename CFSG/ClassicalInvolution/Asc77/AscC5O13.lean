module

public import CFSG.ClassicalInvolution.Asc77.AscC5O12
public import CFSG.ClassicalInvolution.Asc77.AscC5OM21
public import CFSG.ClassicalInvolution.Asc77.AscC5OM33

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

variable (p f : ℕ) [Fact p.Prime]

theorem c25_11Om5_proved : C25Y.C25_11Ω5 p f :=
  c25_11Om5_of (modelFacts_proved p f) (m8gFacts_proved p f)

end CFSG.ClassicalInvolution.Asc77.C5O
