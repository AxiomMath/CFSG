module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P1_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.PG10P1

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 20) = true := by quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 209) (nat_lit 853712) (nat_lit 825792) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 853712) = true := by quickRfl

end CFSG.KD.PG10P1

end
