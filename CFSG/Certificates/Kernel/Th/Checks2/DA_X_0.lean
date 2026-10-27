module

public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.Data.DA_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.DB_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

theorem CFSG.KD.ThA.xLet : CFSG.KC.Th.DceS.lettersOK CFSG.KD.ThA.LT CFSG.KD.ThA.LC CFSG.KD.ThA.LI
    CFSG.KD.ThA.TL CFSG.KD.ThA.VL CFSG.KD.ThA.NL = true := by
  quickRfl

theorem CFSG.KD.ThA.xRel : CFSG.KC.Th.DceS.relsOK CFSG.KD.ThA.RR CFSG.KD.ThA.LT CFSG.KD.ThA.LC
    CFSG.KD.ThA.TL CFSG.KD.ThA.VL CFSG.KD.ThA.NL CFSG.KD.ThA.RH CFSG.KD.ThA.NR = true := by
  quickRfl

theorem CFSG.KD.ThA.xWords : CFSG.KC.Th.DceS.wordsOK CFSG.KD.ThA.WD CFSG.KD.ThA.RR CFSG.KD.ThA.LI
    CFSG.KD.ThA.NL CFSG.KD.ThA.NR CFSG.KD.ThA.WH CFSG.KD.ThA.nW = true := by
  quickRfl

theorem CFSG.KD.ThA.xUsq : CFSG.KC.Th.DceS.usqOK CFSG.KD.ThA.RR CFSG.KD.ThA.LT CFSG.KD.ThA.LI
    CFSG.KD.ThA.TL CFSG.KD.ThA.VL CFSG.KD.ThA.NL CFSG.KD.ThA.NR CFSG.KD.ThA.USQ CFSG.KD.ThA.W
    CFSG.KD.ThA.Wi CFSG.KD.ThA.UH = true := by
  quickRfl

theorem CFSG.KD.ThA.xSel : CFSG.KC.Th.DceS.selOK CFSG.KD.ThA.NB CFSG.KD.ThA.sel = true := by
  quickRfl

theorem CFSG.KD.ThA.xOm : Nat.beq CFSG.KD.ThA.om (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul
    (nat_lit 24) CFSG.KD.ThA.NB)) (nat_lit 1)) = true := by
  quickRfl

theorem CFSG.KD.ThA.xOsh : Nat.beq CFSG.KD.ThA.owd (Nat.mul (nat_lit 24) CFSG.KD.ThA.NB) = true :=
    by
  quickRfl

theorem CFSG.KD.ThA.xI0 : Nat.blt CFSG.KD.ThA.I0 CFSG.KD.ThA.NO = true := by
  quickRfl

theorem CFSG.KD.ThA.xT5 : Nat.beq (Nat.mul CFSG.KD.ThA.nT CFSG.KD.ThA.NO) CFSG.KD.ThA.NORD = true :=
    by
  quickRfl

theorem CFSG.KD.ThA.xSum : CFSG.KC.Th.DceS.sumOK CFSG.KD.ThA.AL CFSG.KD.ThA.MD CFSG.KD.ThA.ND
    CFSG.KD.ThA.NORD CFSG.KD.ThA.SUM = true := by
  quickRfl

theorem CFSG.KD.ThA.xE1 : CFSG.KC.Th.DceS.stabStart CFSG.KD.ThA.E1 = true := by
  quickRfl

theorem CFSG.KD.ThA.xE2 : CFSG.KC.Th.DceS.stabStart CFSG.KD.ThA.E2 = true := by
  quickRfl

theorem CFSG.KD.ThA.xLetA : CFSG.KC.Th.DceS.lettersSub CFSG.KD.ThA.LT CFSG.KD.ThA.LC CFSG.KD.ThA.TL
    CFSG.KD.ThA.VL CFSG.KD.ThA.NL CFSG.KD.ThB.LT = true := by
  quickRfl

theorem CFSG.KD.ThA.xComm : CFSG.KC.Th.DceS.commOK CFSG.KD.ThA.LT CFSG.KD.ThA.TL CFSG.KD.ThA.VL
    CFSG.KD.ThA.NL (CFSG.KC.Th.DceS.let24 CFSG.KD.ThB.LT (nat_lit 0)) = true := by
  quickRfl

theorem CFSG.KD.ThA.xClassA : Nat.beq (CFSG.KC.Th.DceS.mat CFSG.KD.ThA.CB (nat_lit 0))
    (CFSG.KC.Th.DceS.let24 CFSG.KD.ThB.LT (nat_lit 0)) = true := by
  quickRfl

theorem CFSG.KD.ThA.xNord : CFSG.KC.Th.andB (Nat.beq (Nat.mod (Nat.mul CFSG.KD.ThK1.nLive
    CFSG.KD.ThK3.nLive) CFSG.KD.ThA.NCL) (nat_lit 0)) (Nat.beq CFSG.KD.ThA.NORD (Nat.div (Nat.mul
    CFSG.KD.ThK1.nLive CFSG.KD.ThK3.nLive) CFSG.KD.ThA.NCL)) = true := by
  quickRfl

end
