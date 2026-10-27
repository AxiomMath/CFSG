module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Th.S.Data.K1_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

theorem CFSG.KD.ThK1.sH0 : CFSG.KC.LceS.wordsOK CFSG.KD.ThK1.selWT CFSG.KD.ThK1.selRT
    CFSG.KD.ThK1.selST CFSG.KD.ThK1.INV CFSG.KD.ThK1.INV8 (nat_lit 256) CFSG.KD.ThK1.HS = true := by
  quickRfl

theorem CFSG.KD.ThK1.sH1 : CFSG.KC.LceS.invOK CFSG.KD.ThK1.INV CFSG.KD.ThK1.INV8 (nat_lit 10) = true
    := by
  quickRfl

theorem CFSG.KD.ThK1.sH2 : CFSG.KC.LceS.aliveOK CFSG.KD.ThK1.LVs (nat_lit 5) (nat_lit 16923)
    CFSG.KD.ThK1.nLive = true := by
  quickRfl

theorem CFSG.KD.ThK1.sH3 : Nat.beq CFSG.KD.ThK1.nC (nat_lit 16923) = true := by
  quickRfl

theorem CFSG.KD.ThK1.sH4 : CFSG.KC.Th.TcS.litOK CFSG.KD.ThK1.litRT (nat_lit 14) = true := by
  quickRfl

end
