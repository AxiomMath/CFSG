module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.Bind
public import CFSG.Certificates.Kernel.J4.M24Data.M24B_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.M24B

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 2048) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 14) = true := by quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 154) (nat_lit 627001) (nat_lit 443520) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 627001) = true := by quickRfl

theorem hints : CFSG.KC.Bind.hintsOK selWT (nat_lit 2048) (nat_lit 29) (nat_lit 1) HS = true := by
  quickRfl

end CFSG.KD.M24B

end
