module

public import CFSG.ClassicalInvolution.AschTight.T6AW69
public import CFSG.ClassicalInvolution.AschTight.T6AC192
public import CFSG.ClassicalInvolution.AschTight.T6AC194

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.T6A

theorem thm6A_of_c19_main (p f : ℕ) [Fact p.Prime] (hmain : Asc77.C19_main p f) :
    Asc77.Thm6A p f :=
  Asc77.thm6A_of_steps (w69 p f) (c19_2 p f) (c19_4 p f) hmain

end CFSG.ClassicalInvolution.Disconnected.AschTight.T6A
