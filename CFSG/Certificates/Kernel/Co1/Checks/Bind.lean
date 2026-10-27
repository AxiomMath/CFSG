module

public import CFSG.Certificates.Kernel.Common.Bind
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Co1.Data.Co1B
public import CFSG.Certificates.Kernel.Co1.Data.C1_Sel
public import CFSG.Certificates.Kernel.Co1.Data.C2_Sel
public import CFSG.Certificates.Kernel.Co1.Data.C3_Sel
public import CFSG.Certificates.Kernel.Co1.Data.C4_Sel
public import CFSG.Certificates.Kernel.Co1.Data.C5_Sel
public import CFSG.Certificates.Kernel.Co1.Data.C6_Sel
public import CFSG.Certificates.Kernel.Co1.Data.C7_Sel
public import CFSG.Certificates.Kernel.Co1.Data.D1S_0
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.Co1B

theorem bT1 : CFSG.KC.Bind.relsEq CFSG.KD.C1.selRT TOPT (nat_lit 45) (nat_lit 45) HT1 = true := by
  quickRfl

theorem bM12 : Nat.beq M12 (CFSG.KC.Bind.stMap CFSG.KD.C1.selST (nat_lit 7)) = true := by
  quickRfl

theorem b2 : CFSG.KC.Bind.relsSub CFSG.KD.C2.selRT CFSG.KD.C1.selRT M12 (nat_lit 33) (nat_lit 45) H2
    = true := by
  quickRfl

theorem bQ2 : CFSG.KC.Bind.sqOK CFSG.KD.C2.selRT (nat_lit 7) HQ2 = true := by
  quickRfl

theorem bS2 : CFSG.KC.Bind.subsOK CFSG.KD.C2.selRT SB2 (nat_lit 2) true = true := by
  quickRfl

theorem bI3 : Nat.beq IQ3 (CFSG.KC.Bind.invMap QM3 (nat_lit 4)) = true := by
  quickRfl

theorem b3 : CFSG.KC.Bind.relsA (CFSG.KC.Bind.lceN CFSG.KD.C3.selRT) (CFSG.KC.Bind.lceW
    CFSG.KD.C3.selRT) CFSG.KD.C2.selRT SB2 (nat_lit 2) IQ3 (nat_lit 2) (nat_lit 18) (nat_lit 33) H3
    = true := by
  quickRfl

theorem bM34 : Nat.beq M34 (CFSG.KC.Bind.stMap CFSG.KD.C3.selST (nat_lit 3)) = true := by
  quickRfl

theorem b4 : CFSG.KC.Bind.relsSub CFSG.KD.C4.selRT CFSG.KD.C3.selRT M34 (nat_lit 8) (nat_lit 18) H4
    = true := by
  quickRfl

theorem bM56 : Nat.beq M56 (CFSG.KC.Bind.stMap CFSG.KD.C5.selST (nat_lit 2)) = true := by
  quickRfl

theorem b6 : CFSG.KC.Bind.relsSub CFSG.KD.C6.selRT CFSG.KD.C5.selRT M56 (nat_lit 3) (nat_lit 19) H6
    = true := by
  quickRfl

theorem b7 : CFSG.KC.Bind.relsEq CFSG.KD.C7.selRT CFSG.KD.C5.selRT (nat_lit 19) (nat_lit 19) H7 =
    true := by
  quickRfl

theorem bID : Nat.beq IQD (CFSG.KC.Bind.invMap QMD CFSG.KD.D1S.NL) = true := by
  quickRfl

theorem bD : CFSG.KC.Bind.relsA (CFSG.KC.Bind.dceN CFSG.KD.D1S.RT) (CFSG.KC.Bind.dceW
    CFSG.KD.D1S.RT) CFSG.KD.C2.selRT SB2 (nat_lit 2) IQD (nat_lit 1) CFSG.KD.D1S.NR (nat_lit 33) HD
    = true := by
  quickRfl

theorem bM2S : Nat.beq M2S (CFSG.KC.Bind.stMap CFSG.KD.C2.selST (nat_lit 6)) = true := by
  quickRfl

theorem bLD : CFSG.KC.Bind.levelOK CFSG.KD.C2.selST CFSG.KD.C2.selRT M2S QMD CFSG.KD.D1S.NL
    (nat_lit 6) SB2 (nat_lit 2) = true := by
  quickRfl

theorem bHC1 : CFSG.KC.Bind.hintsOK CFSG.KD.C1.selWT (nat_lit 512) (nat_lit 45) (nat_lit 7)
    CFSG.KD.C1.HS = true := by
  quickRfl

theorem bAC1 : CFSG.KC.LceS.aliveOK CFSG.KD.C1.LVs (nat_lit 25) CFSG.KD.C1.nC nAC1 = true := by
  quickRfl

theorem bHC2 : CFSG.KC.Bind.hintsOK CFSG.KD.C2.selWT (nat_lit 512) (nat_lit 33) (nat_lit 6)
    CFSG.KD.C2.HS = true := by
  quickRfl

theorem bAC2 : CFSG.KC.LceS.aliveOK CFSG.KD.C2.LVs (nat_lit 34) CFSG.KD.C2.nC nAC2 = true := by
  quickRfl

theorem bHC3 : CFSG.KC.Bind.hintsOK CFSG.KD.C3.selWT (nat_lit 128) (nat_lit 18) (nat_lit 3)
    CFSG.KD.C3.HS = true := by
  quickRfl

theorem bAC3 : CFSG.KC.LceS.aliveOK CFSG.KD.C3.LVs (nat_lit 2) CFSG.KD.C3.nC nAC3 = true := by
  quickRfl

theorem bHC4 : CFSG.KC.Bind.hintsOK CFSG.KD.C4.selWT (nat_lit 32) (nat_lit 8) (nat_lit 0)
    CFSG.KD.C4.HS = true := by
  quickRfl

theorem bAC4 : CFSG.KC.LceS.aliveOK CFSG.KD.C4.LVs (nat_lit 1) CFSG.KD.C4.nC nAC4 = true := by
  quickRfl

theorem bHC5 : CFSG.KC.Bind.hintsOK CFSG.KD.C5.selWT (nat_lit 512) (nat_lit 19) (nat_lit 2)
    CFSG.KD.C5.HS = true := by
  quickRfl

theorem bAC5 : CFSG.KC.LceS.aliveOK CFSG.KD.C5.LVs (nat_lit 2) CFSG.KD.C5.nC nAC5 = true := by
  quickRfl

theorem bHC6 : CFSG.KC.Bind.hintsOK CFSG.KD.C6.selWT (nat_lit 4) (nat_lit 3) (nat_lit 0)
    CFSG.KD.C6.HS = true := by
  quickRfl

theorem bAC6 : CFSG.KC.LceS.aliveOK CFSG.KD.C6.LVs (nat_lit 1) CFSG.KD.C6.nC nAC6 = true := by
  quickRfl

theorem bHC7 : CFSG.KC.Bind.hintsOK CFSG.KD.C7.selWT (nat_lit 256) (nat_lit 19) (nat_lit 3)
    CFSG.KD.C7.HS = true := by
  quickRfl

theorem bAC7 : CFSG.KC.LceS.aliveOK CFSG.KD.C7.LVs (nat_lit 1) CFSG.KD.C7.nC nAC7 = true := by
  quickRfl

end CFSG.KD.Co1B

end
