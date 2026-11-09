module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.J4.M24Chain.Data.S2_Sel
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.M24S2

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 128) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 14) = true := by
  quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 1) (nat_lit 26) (nat_lit 23) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 26) = true := by
  quickRfl

end CFSG.KD.M24S2

end
