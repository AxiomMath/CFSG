module

public import CFSG.Certificates.Kernel.Th.S.SurjS
public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.Surj_const
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KC.Th.SurjK

open CFSG.KC.Th CFSG.KC.Th.SurjS CFSG.KD.ThS

theorem text : textOK CFSG.KD.ThSj.RB rm CFSG.KD.ThSj.LI = true := by quickRfl

theorem regs : regsOK CFSG.KD.ThSj.RB c rm ONE = true := by quickRfl

theorem rels : BigS.relsOK CFSG.KD.ThSj.RB c rm ONE GR IR = true := by quickRfl

theorem words : wordsOK CFSG.KD.ThSj.LS [CFSG.KD.ThSj.S0, CFSG.KD.ThSj.S1] = true := by quickRfl

theorem std0 : Nat.beq (wordV CFSG.KD.ThSj.RB c rm CFSG.KD.ThSj.S0 ONE) CFSG.KD.ThSeed.SA = true := by
  quickRfl

theorem std1 : Nat.beq (wordV CFSG.KD.ThSj.RB c rm CFSG.KD.ThSj.S1 ONE) CFSG.KD.ThSeed.SB = true := by
  quickRfl

theorem text_neg : BigS.notB (textOK (fun k => Nat.xor (CFSG.KD.ThSj.RB k) 1) rm CFSG.KD.ThSj.LI) = true := by
  quickRfl

theorem regs_neg : BigS.notB (regsOK (fun k => Bool.rec (motive := fun _ => Nat) (CFSG.KD.ThSj.RB k)
    (CFSG.KD.ThSj.RB 2) (Nat.beq k 9)) c rm ONE) = true := by
  quickRfl

theorem rels_neg : BigS.notB (BigS.relsOK (fun k => Bool.rec (motive := fun _ => Nat) (CFSG.KD.ThSj.RB k)
    (CFSG.KD.ThSj.RB 2) (Nat.beq k 1)) c rm ONE GR IR) = true := by
  quickRfl

theorem words_neg : BigS.notB (wordsOK CFSG.KD.ThSj.LS [CFSG.KD.ThSj.S1, CFSG.KD.ThSj.S0]) = true := by
  quickRfl

theorem std_neg : BigS.notB (Nat.beq (wordV CFSG.KD.ThSj.RB c rm CFSG.KD.ThSj.S0 ONE) CFSG.KD.ThSeed.SB) = true := by
  quickRfl

end CFSG.KC.Th.SurjK

end
