module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.J4.M24Chain.Data.S1_Sel
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.M24S1

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 8) = true := by
  quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 30) (nat_lit 120086) (nat_lit 88704) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 120086) = true := by
  quickRfl

end CFSG.KD.M24S1

end
