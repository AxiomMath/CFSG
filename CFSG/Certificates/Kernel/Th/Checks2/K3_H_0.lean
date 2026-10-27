module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Th.S.Data.K3_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

theorem CFSG.KD.ThK3.sH0 : CFSG.KC.LceS.wordsOK CFSG.KD.ThK3.selWT CFSG.KD.ThK3.selRT
    CFSG.KD.ThK3.selST CFSG.KD.ThK3.INV CFSG.KD.ThK3.INV8 (nat_lit 512) CFSG.KD.ThK3.HS = true := by
  quickRfl

theorem CFSG.KD.ThK3.sH1 : CFSG.KC.LceS.invOK CFSG.KD.ThK3.INV CFSG.KD.ThK3.INV8 (nat_lit 14) = true
    := by
  quickRfl

theorem CFSG.KD.ThK3.sH2 : CFSG.KC.LceS.aliveOK CFSG.KD.ThK3.LVs (nat_lit 27) (nat_lit 106919)
    CFSG.KD.ThK3.nLive = true := by
  quickRfl

theorem CFSG.KD.ThK3.sH3 : Nat.beq CFSG.KD.ThK3.nC (nat_lit 106919) = true := by
  quickRfl

theorem CFSG.KD.ThK3.sH4 : CFSG.KC.Th.TcS.litOK CFSG.KD.ThK3.litRT (nat_lit 27) = true := by
  quickRfl

end
