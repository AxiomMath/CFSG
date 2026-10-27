module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.LabF
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.T_Sel
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.B_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.CJSuz2T

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 2048) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 10) = true := by quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 72) (nat_lit 293298) nLive = true := by quickRfl

theorem sH3 : Nat.beq nC (nat_lit 293298) = true := by quickRfl

theorem sH6 : CFSG.KC.LabF.hintsLt selWT (nat_lit 2048) (nat_lit 1) HS = true := by quickRfl

end CFSG.KD.CJSuz2T

namespace CFSG.KD.CJSuz2B

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 8) HS = true := by quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 2) = true := by quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 1) (nat_lit 1) nLive = true := by quickRfl

theorem sH3 : Nat.beq nC (nat_lit 1) = true := by quickRfl

end CFSG.KD.CJSuz2B

end
