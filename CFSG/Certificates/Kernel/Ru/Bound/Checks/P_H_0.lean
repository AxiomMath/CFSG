module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Ru.Bound.Data.P_Sel
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.RuBP

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 6) = true := by
  quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 7) (nat_lit 28102) nLive = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 28102) = true := by
  quickRfl

theorem sH4 : CFSG.KC.RuB.litOK litRT CFSG.KC.RuB.rel (nat_lit 12) = true := by
  quickRfl

theorem sH5 : CFSG.KC.RuB.litOK litST CFSG.KC.RuB.sub (nat_lit 2) = true := by
  quickRfl

end CFSG.KD.RuBP

end
