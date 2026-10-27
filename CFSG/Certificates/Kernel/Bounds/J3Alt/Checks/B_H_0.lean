module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.LabF
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Data.B_Sel
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.J3AB

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 4) = true := by
  quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 4) (nat_lit 14659) nLive = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 14659) = true := by
  quickRfl

end CFSG.KD.J3AB

end
