module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Ru.Bound.Lab
public import CFSG.Certificates.Kernel.Fi22.Bound.Data.P_Sel
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.Fi22BP

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 1024) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 4) = true := by
  quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 9) (nat_lit 34880) nLive = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 34880) = true := by
  quickRfl

theorem sH4 : CFSG.KC.RuB.litOK litRT CFSG.KC.Fi22B.rel (nat_lit 13) = true := by
  quickRfl

theorem sH5 : CFSG.KC.RuB.litOK litST CFSG.KC.Fi22B.sub (nat_lit 7) = true := by
  quickRfl

end CFSG.KD.Fi22BP

end
