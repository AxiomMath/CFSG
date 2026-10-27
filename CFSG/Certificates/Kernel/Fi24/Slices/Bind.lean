module

public import CFSG.Certificates.Kernel.Common.Bind
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Fi24.Data.Fi24B
public import CFSG.Certificates.Kernel.Fi24.Data.F1_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F2_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F3_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F4_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F5_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F6_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F7_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F8_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F9_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F10_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F11_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Fi24B

open CFSG.KC.Bind CFSG.KC.LceS

theorem bT1 : relsEq CFSG.KD.F1.selRT TOPT (nat_lit 80) (nat_lit 80) HT1 = true := by quickRfl

theorem bSF : subsOK CFSG.KD.F1.selRT SBF (nat_lit 1) false = true := by quickRfl

theorem bMF1 : Nat.beq MF1 (stMap CFSG.KD.F1.selST (nat_lit 10)) = true := by quickRfl

theorem bF2 :
    relsF CFSG.KD.F2.selRT CFSG.KD.F1.selRT SBF (nat_lit 1) MF1 (nat_lit 66) (nat_lit 80) HF2 =
      true := by
  quickRfl

theorem bMF2 : Nat.beq MF2 (stMap CFSG.KD.F2.selST (nat_lit 9)) = true := by quickRfl

theorem bF3 : relsSub CFSG.KD.F3.selRT CFSG.KD.F2.selRT MF2 (nat_lit 55) (nat_lit 66) HF3 = true := by
  quickRfl

theorem bMF3 : Nat.beq MF3 (stMap CFSG.KD.F3.selST (nat_lit 8)) = true := by quickRfl

theorem bF4 : relsSub CFSG.KD.F4.selRT CFSG.KD.F3.selRT MF3 (nat_lit 45) (nat_lit 55) HF4 = true := by
  quickRfl

theorem bMF4 : Nat.beq MF4 (stMap CFSG.KD.F4.selST (nat_lit 7)) = true := by quickRfl

theorem bF5 : relsSub CFSG.KD.F5.selRT CFSG.KD.F4.selRT MF4 (nat_lit 36) (nat_lit 45) HF5 = true := by
  quickRfl

theorem bMF5 : Nat.beq MF5 (stMap CFSG.KD.F5.selST (nat_lit 6)) = true := by quickRfl

theorem bF6 : relsSub CFSG.KD.F6.selRT CFSG.KD.F5.selRT MF5 (nat_lit 21) (nat_lit 36) HF6 = true := by
  quickRfl

theorem bMF6 : Nat.beq MF6 (stMap CFSG.KD.F6.selST (nat_lit 5)) = true := by quickRfl

theorem bF7 : relsSub CFSG.KD.F7.selRT CFSG.KD.F6.selRT MF6 (nat_lit 15) (nat_lit 21) HF7 = true := by
  quickRfl

theorem bMF7 : Nat.beq MF7 (stMap CFSG.KD.F7.selST (nat_lit 4)) = true := by quickRfl

theorem bF8 : relsSub CFSG.KD.F8.selRT CFSG.KD.F7.selRT MF7 (nat_lit 10) (nat_lit 15) HF8 = true := by
  quickRfl

theorem bMF8 : Nat.beq MF8 (stMap CFSG.KD.F8.selST (nat_lit 3)) = true := by quickRfl

theorem bF9 : relsSub CFSG.KD.F9.selRT CFSG.KD.F8.selRT MF8 (nat_lit 6) (nat_lit 10) HF9 = true := by
  quickRfl

theorem bMF9 : Nat.beq MF9 (stMap CFSG.KD.F9.selST (nat_lit 2)) = true := by quickRfl

theorem bF10 : relsSub CFSG.KD.F10.selRT CFSG.KD.F9.selRT MF9 (nat_lit 3) (nat_lit 6) HF10 = true := by
  quickRfl

theorem bMF10 : Nat.beq MF10 (stMap CFSG.KD.F10.selST (nat_lit 1)) = true := by quickRfl

theorem bF11 : relsSub CFSG.KD.F11.selRT CFSG.KD.F10.selRT MF10 (nat_lit 1) (nat_lit 3) HF11 = true := by
  quickRfl

theorem bHF1 : hintsOK CFSG.KD.F1.selWT (nat_lit 512) (nat_lit 80) (nat_lit 10) CFSG.KD.F1.HS = true := by
  quickRfl

theorem bAF1 : aliveOK CFSG.KD.F1.LVs (nat_lit 117) CFSG.KD.F1.nC nAF1 = true := by quickRfl

theorem bHF2 : hintsOK CFSG.KD.F2.selWT (nat_lit 1024) (nat_lit 66) (nat_lit 9) CFSG.KD.F2.HS = true := by
  quickRfl

theorem bAF2 : aliveOK CFSG.KD.F2.LVs (nat_lit 227) CFSG.KD.F2.nC nAF2 = true := by quickRfl

theorem bHF3 : hintsOK CFSG.KD.F3.selWT (nat_lit 512) (nat_lit 55) (nat_lit 8) CFSG.KD.F3.HS = true := by
  quickRfl

theorem bAF3 : aliveOK CFSG.KD.F3.LVs (nat_lit 12) CFSG.KD.F3.nC nAF3 = true := by quickRfl

theorem bHF4 : hintsOK CFSG.KD.F4.selWT (nat_lit 128) (nat_lit 45) (nat_lit 7) CFSG.KD.F4.HS = true := by
  quickRfl

theorem bAF4 : aliveOK CFSG.KD.F4.LVs (nat_lit 1) CFSG.KD.F4.nC nAF4 = true := by quickRfl

theorem bHF5 : hintsOK CFSG.KD.F5.selWT (nat_lit 128) (nat_lit 36) (nat_lit 6) CFSG.KD.F5.HS = true := by
  quickRfl

theorem bAF5 : aliveOK CFSG.KD.F5.LVs (nat_lit 1) CFSG.KD.F5.nC nAF5 = true := by quickRfl

theorem bHF6 : hintsOK CFSG.KD.F6.selWT (nat_lit 64) (nat_lit 21) (nat_lit 5) CFSG.KD.F6.HS = true := by
  quickRfl

theorem bAF6 : aliveOK CFSG.KD.F6.LVs (nat_lit 1) CFSG.KD.F6.nC nAF6 = true := by quickRfl

theorem bHF7 : hintsOK CFSG.KD.F7.selWT (nat_lit 32) (nat_lit 15) (nat_lit 4) CFSG.KD.F7.HS = true := by
  quickRfl

theorem bAF7 : aliveOK CFSG.KD.F7.LVs (nat_lit 1) CFSG.KD.F7.nC nAF7 = true := by quickRfl

theorem bHF8 : hintsOK CFSG.KD.F8.selWT (nat_lit 32) (nat_lit 10) (nat_lit 3) CFSG.KD.F8.HS = true := by
  quickRfl

theorem bAF8 : aliveOK CFSG.KD.F8.LVs (nat_lit 1) CFSG.KD.F8.nC nAF8 = true := by quickRfl

theorem bHF9 : hintsOK CFSG.KD.F9.selWT (nat_lit 16) (nat_lit 6) (nat_lit 2) CFSG.KD.F9.HS = true := by
  quickRfl

theorem bAF9 : aliveOK CFSG.KD.F9.LVs (nat_lit 1) CFSG.KD.F9.nC nAF9 = true := by quickRfl

theorem bHF10 : hintsOK CFSG.KD.F10.selWT (nat_lit 4) (nat_lit 3) (nat_lit 1) CFSG.KD.F10.HS = true := by
  quickRfl

theorem bAF10 : aliveOK CFSG.KD.F10.LVs (nat_lit 1) CFSG.KD.F10.nC nAF10 = true := by quickRfl

theorem bHF11 : hintsOK CFSG.KD.F11.selWT (nat_lit 2) (nat_lit 1) (nat_lit 0) CFSG.KD.F11.HS = true := by
  quickRfl

theorem bAF11 : aliveOK CFSG.KD.F11.LVs (nat_lit 1) CFSG.KD.F11.nC nAF11 = true := by quickRfl

end CFSG.KD.Fi24B

end
