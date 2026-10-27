module

public import CFSG.Certificates.Kernel.Bounds.J3Alt.Data.B_Sel
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Data.T_Sel
public import CFSG.Certificates.Kernel.Common.LabF
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.RelNorm
import CFSG.Certificates.Kernel.Bounds.J3Alt.Checks.T_H_0
import CFSG.Certificates.Kernel.Bounds.J3Alt.Checks.B_H_0

public section

namespace CFSG.KC.J3A.Route

theorem norm_T : CFSG.KC.relsNorm CFSG.KD.J3AT.selRT (nat_lit 8) = true := by quickRfl

theorem norm_B : CFSG.KC.relsNorm CFSG.KD.J3AB.selRT (nat_lit 30) = true := by quickRfl

@[expose] def kT : Nat := 2

theorem link_T_hints : CFSG.KC.LabF.hintsLt CFSG.KD.J3AT.selWT (nat_lit 256) kT CFSG.KD.J3AT.HS = true :=
  CFSG.KD.J3AT.sH6

theorem link_T_letters : CFSG.KC.LceS.invOK CFSG.KD.J3AB.INV CFSG.KD.J3AB.INV8 (Nat.mul (nat_lit 2) kT) = true :=
  CFSG.KD.J3AB.sH1

noncomputable def invBf : Nat :=
  Nat.add (Nat.sub CFSG.KD.J3AB.INV (Nat.add (Nat.shiftLeft (nat_lit 65535) (nat_lit 64)) (Nat.shiftLeft (nat_lit 65535) (nat_lit 80))))
    (Nat.add (Nat.shiftLeft (nat_lit 5) (nat_lit 64)) (Nat.shiftLeft (nat_lit 4) (nat_lit 80)))

noncomputable def inv8Bf : Nat :=
  Nat.add (Nat.sub CFSG.KD.J3AB.INV8 (Nat.add (Nat.shiftLeft (nat_lit 254) (nat_lit 32)) (Nat.shiftLeft (nat_lit 254) (nat_lit 40))))
    (Nat.add (Nat.shiftLeft (nat_lit 5) (nat_lit 32)) (Nat.shiftLeft (nat_lit 4) (nat_lit 40)))

theorem link_T_old : CFSG.KC.LceS.invOK invBf inv8Bf (nat_lit 6) = true := by quickRfl

theorem link_T_rejected : CFSG.KC.notB (CFSG.KC.LceS.invOK invBf inv8Bf (Nat.mul (nat_lit 2) kT)) = true := by
  quickRfl


theorem bot_sub : Nat.beq (CFSG.KD.J3AB.selST (nat_lit 0)) (nat_lit 4) = true := by quickRfl

theorem bot_pow : Nat.beq (CFSG.KD.J3AB.selRT (nat_lit 0)) (nat_lit 8) = true := by quickRfl

@[expose] noncomputable def powE (e k : Nat) : Nat :=
  (fun n W => Nat.add (Nat.mul (Nat.mul (nat_lit 4) n) k)
    (Nat.shiftLeft (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.lor acc (Nat.shiftLeft W (Nat.mul (Nat.mul (nat_lit 8) n) i))) k) (nat_lit 12)))
    (Nat.land (Nat.shiftRight e (nat_lit 2)) (nat_lit 1023)) (Nat.shiftRight e (nat_lit 12))

@[expose] def kPow : Nat := 2

theorem bot_pow_k : Nat.beq (CFSG.KD.J3AB.selRT (nat_lit 0)) (powE (CFSG.KD.J3AB.selST (nat_lit 0)) kPow) = true := by
  quickRfl

theorem order_old : Nat.beq (Nat.mul (Nat.mul CFSG.KD.J3AT.nLive CFSG.KD.J3AB.nLive) (nat_lit 3)) (nat_lit 75349440) = true := by quickRfl

theorem pow_forged_rejected : Bool.rec (motive := fun _ => Bool) true false
    (Nat.beq (CFSG.KD.J3AB.selRT (nat_lit 0)) (powE (CFSG.KD.J3AB.selST (nat_lit 0)) (nat_lit 3))) = true := by
  quickRfl

theorem order : Nat.beq (Nat.mul (Nat.mul CFSG.KD.J3AT.nLive CFSG.KD.J3AB.nLive) kPow) (nat_lit 50232960) = true := by quickRfl

end CFSG.KC.J3A.Route

end
