module

public import CFSG.Certificates.Kernel.Common.DceS
public import CFSG.Certificates.Kernel.Common.Bind
public import CFSG.Certificates.Kernel.Co1.Model
public import CFSG.Certificates.Kernel.Co1.Data.D1S_0
public import CFSG.Certificates.Kernel.Co1.Data.Co1B
public import CFSG.Certificates.Kernel.Co1.Data.C3_Sel
public import CFSG.Certificates.Kernel.Co1.Data.C5_Sel
public import CFSG.Certificates.Kernel.Co1.Data.C7_Sel
public import CFSG.Certificates.Kernel.Co1.Data.M1S_0
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.M1S

theorem sM0 : CFSG.KC.Co1M.mpOK MPT (nat_lit 4) = true := by
  quickRfl

theorem sM1 : Nat.beq MM3 (CFSG.KC.Bind.compMap CFSG.KD.Co1B.IQ3 CFSG.KD.Co1B.QM3 (nat_lit 4)) =
    true := by
  quickRfl

theorem sM2 : Nat.beq MM5 (CFSG.KC.Bind.compMap CFSG.KD.Co1B.IQ3 CFSG.KD.Co1B.QM5 (nat_lit 3)) =
    true := by
  quickRfl

theorem sM3 : Nat.beq MMD (CFSG.KC.Bind.compMap CFSG.KD.Co1B.IQ3 CFSG.KD.Co1B.QMD CFSG.KD.D1S.NL) =
    true := by
  quickRfl

theorem sM4 : Nat.beq MD7 (CFSG.KC.Bind.compMap CFSG.KD.Co1B.IQD CFSG.KD.Co1B.QM5 (nat_lit 3)) =
    true := by
  quickRfl

theorem sM5 : CFSG.KC.Co1M.d1LetOK CFSG.KD.D1S.LT MPT CFSG.KD.D1S.NL CFSG.KD.D1S.TL MMD = true := by
  quickRfl

theorem sM6 : CFSG.KC.Co1M.relsOK MPT CFSG.KD.C3.selRT MM3 (nat_lit 18) = true := by
  quickRfl

theorem sM7 : CFSG.KC.Co1M.relsOK MPT CFSG.KD.C5.selRT MM5 (nat_lit 19) = true := by
  quickRfl

theorem sM8 : CFSG.KC.Co1M.tFixOK MPT CFSG.KD.C7.selST CFSG.KD.D1S.PBT CFSG.KD.D1S.OMT MM5
    (nat_lit 3) CFSG.KD.D1S.NB CFSG.KD.D1S.I0 = true := by
  quickRfl

theorem sM9 : CFSG.KC.Loop.allBelow CFSG.KD.D1S.NO (nat_lit 27) (CFSG.KC.Co1M.omClosOK
    CFSG.KD.D1S.LT CFSG.KD.D1S.PBT CFSG.KD.D1S.OMT OHT CFSG.KD.D1S.NL CFSG.KD.D1S.TL CFSG.KD.D1S.NB
    CFSG.KD.D1S.NO) = true := by
  quickRfl

theorem sM10 : CFSG.KC.Co1M.centOK CFSG.KD.D1S.RT CFSG.KD.C7.selST MD7 CFSG.KD.D1S.TL (nat_lit 3) CH
    = true := by
  quickRfl

theorem sM11 : Nat.beq (CFSG.KC.DceS.eCnt (CFSG.KC.DceS.enumRun TTE (CFSG.KC.Co1M.tGens MPT
    CFSG.KD.C7.selST MM5 (nat_lit 3)) (nat_lit 3) nT (nat_lit 0) nT (nat_lit 1))) (Nat.succ nT) =
    true := by
  quickRfl

theorem sM12 : CFSG.KC.andB (Nat.beq (Nat.mod CFSG.KD.D1S.nN nT) (nat_lit 0)) (Nat.beq (Nat.div
    CFSG.KD.D1S.nN nT) CFSG.KD.D1S.NO) = true := by
  quickRfl

end CFSG.KD.M1S

end
