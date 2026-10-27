module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.LabF
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Data.T_Sel
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.J3AT

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 256) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 4) = true := by
  quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 5) (nat_lit 17839) nLive = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 17839) = true := by
  quickRfl

theorem sH4 : CFSG.KC.LabF.litOK litRT CFSG.KC.J3A.rel (nat_lit 8) = true := by
  quickRfl

theorem sH6 : CFSG.KC.LabF.hintsLt selWT (nat_lit 256) (nat_lit 2) HS = true := by
  quickRfl

end CFSG.KD.J3AT

end
