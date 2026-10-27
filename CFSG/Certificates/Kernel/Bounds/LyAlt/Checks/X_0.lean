module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.LyA

open CFSG.KC.LyA.DceS

theorem xConsts : constsOK7 = true := by quickRfl

theorem xAlpha : andB (Nat.beq NL (nat_lit 12)) (andB (Nat.beq TL (nat_lit 10))
    (andB (Nat.beq VL (nat_lit 11)) (Nat.beq LI (nat_lit 0xa0b08090607040502030001)))) = true := by
  quickRfl

theorem xLet : lettersOK LT LI TL VL NL = true := by quickRfl

theorem xRel : andB (Nat.beq NR (nat_lit 53)) (relsOK CFSG.KC.LyA.rel LT TL VL NL NR) = true := by
  quickRfl

theorem xWords : wordsOK WD CFSG.KC.LyA.rel LI NL NR WH nW = true := by quickRfl

theorem xUsq : usqOK CFSG.KC.LyA.rel LT LI TL VL NL NR USQ W Wi UH = true := by quickRfl

theorem xND : Nat.blt ND (nat_lit 255) = true := by quickRfl

theorem xI0 : Nat.blt I0 NO = true := by quickRfl

theorem xNord : Nat.beq NORD (Nat.mul (Nat.mul (nat_lit 3906) (nat_lit 3125)) (nat_lit 480)) = true := by
  quickRfl

theorem xT5 : Nat.beq (Nat.mul nT NO) NORD = true := by quickRfl

theorem xSum : sumOK AL MD ND NORD SUM = true := by quickRfl

theorem xE1 : stabStart E1 = true := by quickRfl

theorem xE2 : stabStart E2 = true := by quickRfl

theorem xE3 : stabStart E3 = true := by quickRfl

theorem xE4 : stabStart E4 = true := by quickRfl

theorem xBound : Nat.beq (Nat.mul NORD SUM) (nat_lit 0xb7e827f2449700) = true := by quickRfl

theorem xAlive : Nat.beq AL (nat_lit 31) = true := by quickRfl

theorem xSub1 : Nat.beq (Nat.div NORD (bits MD (nat_lit 20) (nat_lit 20))) (nat_lit 19530) = true := by
  quickRfl

theorem xSub2 : Nat.beq (Nat.div NORD (bits MD (nat_lit 40) (nat_lit 20))) (nat_lit 968750) = true := by
  quickRfl

theorem xSub3 : Nat.beq (Nat.div NORD (bits MD (nat_lit 60) (nat_lit 20))) (nat_lit 5812500) = true := by
  quickRfl

theorem xSub4 : Nat.beq (Nat.div NORD (bits MD (nat_lit 80) (nat_lit 20))) (nat_lit 2034375) = true := by
  quickRfl

end CFSG.KD.LyA

end
