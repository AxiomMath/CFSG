module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Ru.Bound.Data.C_Sel
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.RuBC

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 6) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 21) = true := by
  quickRfl

theorem sH4 : CFSG.KC.RuB.litOK litRT CFSG.KC.RuB.rel (nat_lit 12) = true := by
  quickRfl

theorem sH5 : CFSG.KC.RuB.litOK litST CFSG.KC.RuB.sub (nat_lit 2) = true := by
  quickRfl

theorem sH6 : CFSG.KC.RuB.hintsLt selWT (nat_lit 512) (nat_lit 2) HS = true := by
  quickRfl

end CFSG.KD.RuBC

end
