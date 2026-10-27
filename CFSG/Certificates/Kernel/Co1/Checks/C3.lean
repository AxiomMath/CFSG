module

public import CFSG.Certificates.Kernel.Co1.Data.C3_Ok
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.C3

theorem okW_all : ∀ t < 15, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 5, okC t = true := by
  kc_cover 1

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 128) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 8) = true := by quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 2) (nat_lit 4480) (nat_lit 4480) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 4480) = true := by quickRfl

end CFSG.KD.C3

end
