module

public import CFSG.Certificates.Kernel.McL.Rels
public import CFSG.Certificates.Kernel.McL.Data.CN_Tab
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.McL.CN

theorem okW_all : ∀ t < 32, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 13, okC t = true := by
  kc_cover 1

theorem sH0 : CFSG.KC.LceS.wordsOK selWT CFSG.KC.McL.Rels.NR1 CFSG.KC.McL.Rels.STQ INV INV8
    (nat_lit 512) HS = true := by quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 6) = true := by quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 5) nC nAlive = true := by quickRfl

end CFSG.KD.McL.CN

end
