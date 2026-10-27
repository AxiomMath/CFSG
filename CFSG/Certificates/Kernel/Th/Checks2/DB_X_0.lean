module

public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.Data.DB_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

theorem CFSG.KD.ThB.xLet : CFSG.KC.Th.DceS.lettersOK CFSG.KD.ThB.LT CFSG.KD.ThB.LC CFSG.KD.ThB.LI
    CFSG.KD.ThB.TL CFSG.KD.ThB.VL CFSG.KD.ThB.NL = true := by
  quickRfl

theorem CFSG.KD.ThB.xRel : CFSG.KC.Th.DceS.relsOK CFSG.KD.ThB.RR CFSG.KD.ThB.LT CFSG.KD.ThB.LC
    CFSG.KD.ThB.TL CFSG.KD.ThB.VL CFSG.KD.ThB.NL CFSG.KD.ThB.RH CFSG.KD.ThB.NR = true := by
  quickRfl

theorem CFSG.KD.ThB.xWords : CFSG.KC.Th.DceS.wordsOK CFSG.KD.ThB.WD CFSG.KD.ThB.RR CFSG.KD.ThB.LI
    CFSG.KD.ThB.NL CFSG.KD.ThB.NR CFSG.KD.ThB.WH CFSG.KD.ThB.nW = true := by
  quickRfl

theorem CFSG.KD.ThB.xUsq : CFSG.KC.Th.DceS.usqOK CFSG.KD.ThB.RR CFSG.KD.ThB.LT CFSG.KD.ThB.LI
    CFSG.KD.ThB.TL CFSG.KD.ThB.VL CFSG.KD.ThB.NL CFSG.KD.ThB.NR CFSG.KD.ThB.USQ CFSG.KD.ThB.W
    CFSG.KD.ThB.Wi CFSG.KD.ThB.UH = true := by
  quickRfl

theorem CFSG.KD.ThB.xSel : CFSG.KC.Th.DceS.selOK CFSG.KD.ThB.NB CFSG.KD.ThB.sel = true := by
  quickRfl

theorem CFSG.KD.ThB.xOm : Nat.beq CFSG.KD.ThB.om (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul
    (nat_lit 24) CFSG.KD.ThB.NB)) (nat_lit 1)) = true := by
  quickRfl

theorem CFSG.KD.ThB.xOsh : Nat.beq CFSG.KD.ThB.owd (Nat.mul (nat_lit 24) CFSG.KD.ThB.NB) = true :=
    by
  quickRfl

theorem CFSG.KD.ThB.xI0 : Nat.blt CFSG.KD.ThB.I0 CFSG.KD.ThB.NO = true := by
  quickRfl

theorem CFSG.KD.ThB.xT5 : Nat.beq (Nat.mul CFSG.KD.ThB.nT CFSG.KD.ThB.NO) (Nat.mul
    CFSG.KD.ThK1.nLive CFSG.KD.ThK3.nLive) = true := by
  quickRfl

theorem CFSG.KD.ThB.xSum : CFSG.KC.Th.DceS.sumOK CFSG.KD.ThB.AL CFSG.KD.ThB.MD CFSG.KD.ThB.ND
    (Nat.mul CFSG.KD.ThK1.nLive CFSG.KD.ThK3.nLive) CFSG.KD.ThB.SUM = true := by
  quickRfl

theorem CFSG.KD.ThB.xE1 : CFSG.KC.Th.DceS.stabStart CFSG.KD.ThB.E1 = true := by
  quickRfl

theorem CFSG.KD.ThB.xE2 : CFSG.KC.Th.DceS.stabStart CFSG.KD.ThB.E2 = true := by
  quickRfl

theorem CFSG.KD.ThB.xE3 : CFSG.KC.Th.DceS.stabStart CFSG.KD.ThB.E3 = true := by
  quickRfl

theorem CFSG.KD.ThB.xE4 : CFSG.KC.Th.DceS.stabStart CFSG.KD.ThB.E4 = true := by
  quickRfl

theorem CFSG.KD.ThB.xE5 : CFSG.KC.Th.DceS.stabStart CFSG.KD.ThB.E5 = true := by
  quickRfl

theorem CFSG.KD.ThB.xE6 : CFSG.KC.Th.DceS.stabStart CFSG.KD.ThB.E6 = true := by
  quickRfl

theorem CFSG.KD.ThB.xE7 : CFSG.KC.Th.DceS.stabStart CFSG.KD.ThB.E7 = true := by
  quickRfl

theorem CFSG.KD.ThB.xE8 : CFSG.KC.Th.DceS.stabStart CFSG.KD.ThB.E8 = true := by
  quickRfl

theorem CFSG.KD.ThB.xE9 : CFSG.KC.Th.DceS.stabStart CFSG.KD.ThB.E9 = true := by
  quickRfl

theorem CFSG.KD.ThB.xE10 : CFSG.KC.Th.DceS.stabStart CFSG.KD.ThB.E10 = true := by
  quickRfl

theorem CFSG.KD.ThB.xLetB : CFSG.KC.Th.andB (Nat.beq CFSG.KD.ThB.NL (nat_lit 16)) (Nat.beq
    CFSG.KD.ThB.LC (nat_lit 20011376718272490338853433276725592320)) = true := by
  quickRfl

theorem CFSG.KD.ThB.xRelB : CFSG.KC.Th.andB (Nat.beq CFSG.KD.ThB.NR (nat_lit 39)) (Nat.beq
    CFSG.KD.ThB.RH (nat_lit
    1243246491195555662985712545119472705112553111610534931758030933907000127540406711912033812736))
    = true := by
  quickRfl

theorem CFSG.KD.ThB.xBound : Nat.beq (Nat.mul (Nat.mul CFSG.KD.ThK1.nLive CFSG.KD.ThK3.nLive)
    CFSG.KD.ThB.SUM) (nat_lit 90745943887872000) = true := by
  quickRfl

end
