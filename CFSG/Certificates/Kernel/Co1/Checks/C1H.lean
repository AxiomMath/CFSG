module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Co1.Data.C1_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.C1

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 16) = true := by quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 25) (nat_lit 99861) (nat_lit 98280) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 99861) = true := by quickRfl

end CFSG.KD.C1

end
