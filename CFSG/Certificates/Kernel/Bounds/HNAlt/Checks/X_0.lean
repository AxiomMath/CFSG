module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.DceSP
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Disp
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

namespace CFSG.KD.HNA

open CFSG.KC.HNA.DceS

theorem xAlpha : andB (Nat.beq NL (nat_lit 9)) (andB (Nat.beq TL (nat_lit 8))
    (andB (Nat.beq VL (nat_lit 8)) (Nat.beq LI (nat_lit 0x80607040502030001)))) = true := by
  quickRfl

theorem xLet : lettersOK LT LI TL VL NL = true := by quickRfl

theorem xRel : andB (Nat.beq NR (nat_lit 19)) (relsOK CFSG.KC.HNA.rel LT TL VL NL NR) = true := by
  quickRfl

theorem xWords : wordsOK WD CFSG.KC.HNA.rel LI NL NR WH nW = true := by quickRfl

theorem xUsq : usqOK CFSG.KC.HNA.rel LT LI TL VL NL NR USQ W Wi UH = true := by quickRfl

theorem xW : andB (Nat.beq W ONEP) (Nat.beq Wi ONEP) = true := by quickRfl

theorem xND : Nat.blt ND (nat_lit 65535) = true := by quickRfl

theorem xI0 : Nat.blt I0 NO = true := by quickRfl

theorem xNord : Nat.beq NORD (Nat.mul (Nat.mul (nat_lit 5) (nat_lit 50)) (nat_lit 10080)) = true := by
  quickRfl

theorem xT5 : Nat.beq (Nat.mul nT NO) NORD = true := by quickRfl

theorem xSum : sumOK AL MD ND NORD SUM = true := by quickRfl

theorem xBound : Nat.beq (Nat.mul NORD SUM) (nat_lit 0xf851f685c000) = true := by quickRfl

theorem xAlive : Nat.beq AL (nat_lit 0x3ffffffffffffffffff7f) = true := by quickRfl

@[expose] noncomputable def okE (D : Nat) : Bool := stabStart (Ed D)

end CFSG.KD.HNA

#kc_each_unfold CFSG.KD.HNA.okE 1 7 as CFSG.KD.HNA.xE

#kc_each_unfold CFSG.KD.HNA.okE 8 82 as CFSG.KD.HNA.xE

end
