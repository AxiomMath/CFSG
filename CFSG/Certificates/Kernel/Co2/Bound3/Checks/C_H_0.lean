module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Co2.Bound3.Data.C_Sel
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.Co2KC

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 2048) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 4) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 660) = true := by
  quickRfl

theorem sH4 : CFSG.KC.Co2K.litOK litRT CFSG.KC.Co2B.rel (nat_lit 10) = true := by
  quickRfl

theorem sH5 : CFSG.KC.Co2K.litOK litST CFSG.KC.Co2K.subH (nat_lit 4) = true := by
  quickRfl

theorem sH6 : CFSG.KC.Co2K.hintsLt selWT (nat_lit 2048) (nat_lit 4) HS = true := by
  quickRfl

end CFSG.KD.Co2KC

end
