module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Ru.Bound.Lab
public import CFSG.Certificates.Kernel.Co2.Bound.Data.P_Sel
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.Co2BP

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 2048) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 4) = true := by
  quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 31) (nat_lit 123652) nLive = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 123652) = true := by
  quickRfl

theorem sH4 : CFSG.KC.RuB.litOK litRT CFSG.KC.Co2B.rel (nat_lit 10) = true := by
  quickRfl

theorem sH5 : CFSG.KC.RuB.litOK litST CFSG.KC.Co2B.sub (nat_lit 7) = true := by
  quickRfl

end CFSG.KD.Co2BP

end
