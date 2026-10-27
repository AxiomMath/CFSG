module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.He.Bound.Data.P_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.HeBP

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 2048) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 4) = true := by quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 139) (nat_lit 567815) nLive = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 567815) = true := by quickRfl

theorem sH4 : CFSG.KC.HeB.litOK litRT CFSG.KC.HeB.rel (nat_lit 7) = true := by quickRfl

theorem sH5 : CFSG.KC.HeB.litOK litST CFSG.KC.HeB.sub (nat_lit 2) = true := by quickRfl

end CFSG.KD.HeBP

end
