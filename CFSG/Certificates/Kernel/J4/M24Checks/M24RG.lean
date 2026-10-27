module

public import Certificates.Data.Kernel.M24Rs
public import Certificates.Data.Kernel.LceSTab
public import CFSG.Certificates.Kernel.J4.M24Data.M24R
public import CFSG.Certificates.Kernel.J4.M24Data.M24B_Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KJ4.M24G

open CFSG.KM24 CFSG.KD.M24R

theorem ranges : mAnd (Nat.beq (Nat.mod (nat_lit 4) (nat_lit 2)) (nat_lit 0))
    (mAnd (Nat.blt (nat_lit 0) (nat_lit 24)) (mAnd (Nat.blt (Nat.mul (nat_lit 24) (nat_lit 4))
      (nat_lit 32768)) (lettersLt R0 (nat_lit 4)))) = true := by quickRfl

theorem init : chkInit T P (nat_lit 4) (nat_lit 24) R0 A0 G0 = true := by quickRfl

theorem rep0 : chkReplayG B0 (nat_lit 120) A0 A1 G0 G1 = true := by quickRfl

theorem rep1 : chkReplayG B1 (nat_lit 120) A1 A2 G1 G2 = true := by quickRfl

theorem rep2 : chkReplayG B2 (nat_lit 1) A2 A3 G2 G3 = true := by quickRfl

theorem next : chkNext N A3 Rn G3 (nat_lit 96) (nat_lit 7) = true := by quickRfl

theorem rt_bind : rtBind CFSG.KD.M24B.selRT Rn (nat_lit 29) (nat_lit 14) = true := by quickRfl

theorem rn_len : Nat.beq (lenR Rn) (nat_lit 29) = true := by quickRfl

theorem st0 : Nat.beq (CFSG.KD.M24B.selST (nat_lit 0)) (nat_lit 8196) = true := by quickRfl

theorem pow7 : mAnd (Nat.beq (Nat.land (Nat.shiftRight (CFSG.KD.M24B.selRT (nat_lit 7)) (nat_lit 2))
    (nat_lit 1023)) (nat_lit 23))
    (allLet (Nat.shiftRight (CFSG.KD.M24B.selRT (nat_lit 7)) (nat_lit 12)) (nat_lit 23) (nat_lit 3)) =
      true := by quickRfl

theorem wt_per : CFSG.Certificates.LCE.wtPer CFSG.KD.M24B.selWT (nat_lit 2048) = true := by quickRfl

theorem rels_norm : CFSG.Certificates.LCE.relsNorm CFSG.KD.M24B.selRT (nat_lit 29) = true := by
  quickRfl

end CFSG.KJ4.M24G

end
