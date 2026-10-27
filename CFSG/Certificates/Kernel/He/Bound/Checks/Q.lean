module

public import CFSG.Certificates.Kernel.He.Bound.Data.Q_Tab
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.HeBQ

theorem okW_all : ∀ t < 38, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 4, okC t = true := by
  kc_cover 1

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 4) = true := by quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 6) (nat_lit 22986) nLive = true := by quickRfl

theorem sH3 : Nat.beq nC (nat_lit 22986) = true := by quickRfl

end CFSG.KD.HeBQ

end
