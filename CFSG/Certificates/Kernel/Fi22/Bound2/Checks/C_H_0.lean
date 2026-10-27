module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.C_Sel
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.Fi22KC

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 4) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 5821) = true := by
  quickRfl

theorem sH4 : CFSG.KC.Fi22K.litOK litRT CFSG.KC.Fi22B.rel (nat_lit 13) = true := by
  quickRfl

theorem sH5 : CFSG.KC.Fi22K.litOK litST CFSG.KC.Fi22K.subY (nat_lit 13) = true := by
  quickRfl

theorem sH6 : CFSG.KC.Fi22K.hintsLt selWT (nat_lit 512) (nat_lit 13) HS = true := by
  quickRfl

end CFSG.KD.Fi22KC

end
