module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Fi24.Data.F1_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.F1

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 24) = true := by quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 117) (nat_lit 478324) (nat_lit 306936) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 478324) = true := by quickRfl

end CFSG.KD.F1

end
