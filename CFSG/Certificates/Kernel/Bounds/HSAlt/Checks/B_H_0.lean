module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.B_Sel
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.HSKB

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 4) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 27006) = true := by
  quickRfl

theorem sH4 : CFSG.KC.HSK.litOK litRT CFSG.KC.HSK.rel (nat_lit 13) = true := by
  quickRfl

theorem sH5 : CFSG.KC.HSK.litOK litST CFSG.KC.HSK.subB (nat_lit 5) = true := by
  quickRfl

end CFSG.KD.HSKB

end
