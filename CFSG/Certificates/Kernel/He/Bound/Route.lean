module

public import CFSG.Certificates.Kernel.He.Bound.Data.P_Sel
public import CFSG.Certificates.Kernel.He.Bound.Data.Q_Sel
public import CFSG.Certificates.Kernel.He.Bound.Data.C_Sel
public import CFSG.Certificates.Kernel.He.Bound.Lab
public import CFSG.Certificates.Kernel.Common.LceS
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.RelNorm
import CFSG.Certificates.Kernel.He.Bound.Checks.C_H_0
import CFSG.Certificates.Kernel.He.Bound.Checks.Q

public section

namespace CFSG.KC.HeB.Route

@[expose] def kC : Nat := 2

theorem link_C_hints : CFSG.KC.HeB.hintsLt CFSG.KD.HeBC.selWT (nat_lit 2048) kC CFSG.KD.HeBC.HS = true :=
  CFSG.KD.HeBC.sH6

theorem link_C_letters : CFSG.KC.LceS.invOK CFSG.KD.HeBQ.INV CFSG.KD.HeBQ.INV8 (Nat.mul (nat_lit 2) kC) = true :=
  CFSG.KD.HeBQ.sH1

noncomputable def invQf : Nat :=
  Nat.add (Nat.sub CFSG.KD.HeBQ.INV (Nat.add (Nat.shiftLeft (nat_lit 65535) (nat_lit 64)) (Nat.shiftLeft (nat_lit 65535) (nat_lit 80))))
    (Nat.add (Nat.shiftLeft (nat_lit 5) (nat_lit 64)) (Nat.shiftLeft (nat_lit 4) (nat_lit 80)))

noncomputable def inv8Qf : Nat :=
  Nat.add (Nat.sub CFSG.KD.HeBQ.INV8 (Nat.add (Nat.shiftLeft (nat_lit 254) (nat_lit 32)) (Nat.shiftLeft (nat_lit 254) (nat_lit 40))))
    (Nat.add (Nat.shiftLeft (nat_lit 5) (nat_lit 32)) (Nat.shiftLeft (nat_lit 4) (nat_lit 40)))

theorem link_C_old : CFSG.KC.LceS.invOK invQf inv8Qf (nat_lit 6) = true := by quickRfl

theorem norm_Q : CFSG.KC.relsNorm CFSG.KD.HeBQ.selRT (nat_lit 6) = true := by quickRfl

theorem link_C_rejected : CFSG.KC.notB (CFSG.KC.LceS.invOK invQf inv8Qf (Nat.mul (nat_lit 2) kC)) = true := by
  quickRfl

theorem q_sq : Nat.beq (CFSG.KD.HeBQ.selRT (nat_lit 0)) (nat_lit 8) = true := by quickRfl

theorem q_sub : Nat.beq (CFSG.KD.HeBQ.selST (nat_lit 0)) (nat_lit 8196) = true := by quickRfl

theorem q_pow : Nat.beq (CFSG.KD.HeBQ.selRT (nat_lit 1)) (nat_lit 13563782407139352) = true := by
  quickRfl

theorem order : Nat.beq (Nat.mul (Nat.mul CFSG.KD.HeBP.nLive CFSG.KD.HeBQ.nLive) (nat_lit 6))
    (nat_lit 4030387200) = true := by quickRfl

end CFSG.KC.HeB.Route

end
