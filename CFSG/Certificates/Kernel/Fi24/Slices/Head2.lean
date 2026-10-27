module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Fi24.Data.F2_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.F2

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 1024) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 20) = true := by quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 227) (nat_lit 929785) (nat_lit 825792) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 929785) = true := by quickRfl

end CFSG.KD.F2

end
