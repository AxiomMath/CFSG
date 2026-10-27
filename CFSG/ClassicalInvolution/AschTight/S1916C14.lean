module

public import CFSG.ClassicalInvolution.AschTight.S1916SC
public import CFSG.ClassicalInvolution.AschTight.S1916NC2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable (p f : ℕ) [Fact p.Prime]

theorem c19_14_of_Z (hZ : C19_14ZTmp p f) (hB3 : GoldschmidtB3Tmp) : C19_14Tmp p f :=
  fun G _ _ _ K z S W hd => not_case2_of p f (c19_14SC_of p f hZ) hB3 G K z S W hd

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
