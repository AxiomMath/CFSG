module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Co1.Data.C2_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.C2

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 14) = true := by quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 34) (nat_lit 135809) (nat_lit 47104) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 135809) = true := by quickRfl

end CFSG.KD.C2

end
