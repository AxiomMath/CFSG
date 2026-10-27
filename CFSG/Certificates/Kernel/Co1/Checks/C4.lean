module

public import CFSG.Certificates.Kernel.Co1.Data.C4_Ok
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.C4

theorem okW_all : ∀ t < 1, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 1, okC t = true := by
  kc_cover 1

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 32) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 6) = true := by quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 1) (nat_lit 72) (nat_lit 72) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 72) = true := by quickRfl

end CFSG.KD.C4

end
