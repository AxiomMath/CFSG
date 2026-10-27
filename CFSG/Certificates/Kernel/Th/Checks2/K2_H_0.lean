module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Th.S.Data.K2_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

theorem CFSG.KD.ThK2.sH0 : CFSG.KC.LceS.wordsOK CFSG.KD.ThK2.selWT CFSG.KD.ThK2.selRT
    CFSG.KD.ThK2.selST CFSG.KD.ThK2.INV CFSG.KD.ThK2.INV8 (nat_lit 512) CFSG.KD.ThK2.HS = true := by
  quickRfl

theorem CFSG.KD.ThK2.sH1 : CFSG.KC.LceS.invOK CFSG.KD.ThK2.INV CFSG.KD.ThK2.INV8 (nat_lit 12) = true
    := by
  quickRfl

theorem CFSG.KD.ThK2.sH2 : CFSG.KC.LceS.aliveOK CFSG.KD.ThK2.LVs (nat_lit 10) (nat_lit 39573)
    CFSG.KD.ThK2.nLive = true := by
  quickRfl

theorem CFSG.KD.ThK2.sH3 : Nat.beq CFSG.KD.ThK2.nC (nat_lit 39573) = true := by
  quickRfl

theorem CFSG.KD.ThK2.sH4 : CFSG.KC.Th.TcS.litOK CFSG.KD.ThK2.litRT (nat_lit 20) = true := by
  quickRfl

end
