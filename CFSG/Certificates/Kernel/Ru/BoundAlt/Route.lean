module

public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.M_Sel
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_Sel
public import CFSG.Certificates.Kernel.Ru.Bound.Data.P_Sel
public import CFSG.Certificates.Kernel.Ru.Bound.Data.C_Sel
public import CFSG.Certificates.Kernel.Ru.Bound.Data.A
public import CFSG.Certificates.Kernel.Ru.Bound.Rels
public import CFSG.Certificates.Kernel.Ru.Bound.Lab
public import CFSG.Certificates.Kernel.Common.LabF
public import CFSG.Certificates.Kernel.McL.Perm
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.RelNorm
import CFSG.Certificates.Kernel.Ru.Bound.Checks.C_H_0
import CFSG.Certificates.Kernel.Ru.BoundAlt.Checks.M_H_0
import CFSG.Certificates.Kernel.Ru.BoundAlt.Checks.B_H_0

public section

namespace CFSG.KC.RuBA

open CFSG.KC

@[expose] noncomputable def qToP (e : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 4) (LceS.wLen e))
    (Nat.shiftLeft (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun q acc => Nat.lor acc (Nat.shiftLeft
        (Nat.add (wLet (LceS.wWord e) q) (Nat.land (wLet (LceS.wWord e) q) (nat_lit 2)))
        (Nat.mul (nat_lit 8) q))) (LceS.wLen e)) (nat_lit 12))

@[expose] noncomputable def derivedOK (k : Nat) : Bool :=
  andB (Nat.beq (qToP (CFSG.KD.RuBAM.selRT (Nat.add (nat_lit 7) k))) (CFSG.KD.RuBA.TW k))
    (Nat.beq (CFSG.KD.RuBA.TL k) (McL.pid CFSG.KD.RuBA.d))

end CFSG.KC.RuBA

namespace CFSG.KC.RuBA.Route

theorem norm_M : CFSG.KC.relsNorm CFSG.KD.RuBAM.selRT (nat_lit 16) = true := by quickRfl
theorem norm_B : CFSG.KC.relsNorm CFSG.KD.RuBAB.selRT (nat_lit 81) = true := by quickRfl

@[expose] def kC : Nat := 2

theorem link_C_hints : CFSG.KC.RuB.hintsLt CFSG.KD.RuBC.selWT (nat_lit 512) kC CFSG.KD.RuBC.HS = true :=
  CFSG.KD.RuBC.sH6

theorem link_C_letters : CFSG.KC.LceS.invOK CFSG.KD.RuBAM.INV CFSG.KD.RuBAM.INV8 (Nat.mul (nat_lit 2) kC) = true :=
  CFSG.KD.RuBAM.sH1

noncomputable def invMf : Nat :=
  Nat.add (Nat.sub CFSG.KD.RuBAM.INV (Nat.add (Nat.shiftLeft (nat_lit 65535) (nat_lit 64)) (Nat.shiftLeft (nat_lit 65535) (nat_lit 80))))
    (Nat.add (Nat.shiftLeft (nat_lit 5) (nat_lit 64)) (Nat.shiftLeft (nat_lit 4) (nat_lit 80)))

noncomputable def inv8Mf : Nat :=
  Nat.add (Nat.sub CFSG.KD.RuBAM.INV8 (Nat.add (Nat.shiftLeft (nat_lit 254) (nat_lit 32)) (Nat.shiftLeft (nat_lit 254) (nat_lit 40))))
    (Nat.add (Nat.shiftLeft (nat_lit 5) (nat_lit 32)) (Nat.shiftLeft (nat_lit 4) (nat_lit 40)))

theorem link_C_old : CFSG.KC.LceS.invOK invMf inv8Mf (nat_lit 6) = true := by quickRfl

theorem link_C_rejected : CFSG.KC.notB (CFSG.KC.LceS.invOK invMf inv8Mf (Nat.mul (nat_lit 2) kC)) = true := by
  quickRfl

@[expose] def kM : Nat := 10

theorem link_M_hints : CFSG.KC.LabF.hintsLt CFSG.KD.RuBAM.selWT (nat_lit 256) kM CFSG.KD.RuBAM.HS = true :=
  CFSG.KD.RuBAM.sH6

theorem link_M_letters : CFSG.KC.LceS.invOK CFSG.KD.RuBAB.INV CFSG.KD.RuBAB.INV8 (Nat.mul (nat_lit 2) kM) = true :=
  CFSG.KD.RuBAB.sH1

noncomputable def invBf : Nat :=
  Nat.add (Nat.sub CFSG.KD.RuBAB.INV (Nat.add (Nat.shiftLeft (nat_lit 65535) (nat_lit 320)) (Nat.shiftLeft (nat_lit 65535) (nat_lit 336))))
    (Nat.add (Nat.shiftLeft (nat_lit 21) (nat_lit 320)) (Nat.shiftLeft (nat_lit 20) (nat_lit 336)))

noncomputable def inv8Bf : Nat :=
  Nat.add (Nat.sub CFSG.KD.RuBAB.INV8 (Nat.add (Nat.shiftLeft (nat_lit 254) (nat_lit 160)) (Nat.shiftLeft (nat_lit 254) (nat_lit 168))))
    (Nat.add (Nat.shiftLeft (nat_lit 21) (nat_lit 160)) (Nat.shiftLeft (nat_lit 20) (nat_lit 168)))

theorem link_M_old : CFSG.KC.LceS.invOK invBf inv8Bf (nat_lit 22) = true := by quickRfl

theorem link_M_rejected : CFSG.KC.notB (CFSG.KC.LceS.invOK invBf inv8Bf (Nat.mul (nat_lit 2) kM)) = true := by
  quickRfl

theorem q_sq : Nat.beq (CFSG.KD.RuBAM.selRT (nat_lit 0)) (nat_lit 2105352) = true := by quickRfl

theorem p_t2 : Nat.beq CFSG.KC.RuB.R1 (nat_lit 4210696) = true := by quickRfl

theorem a_nT : Nat.beq CFSG.KD.RuBA.nT (nat_lit 9) = true := by quickRfl

theorem derived_0 : CFSG.KC.RuBA.derivedOK (nat_lit 0) = true := by quickRfl
theorem derived_1 : CFSG.KC.RuBA.derivedOK (nat_lit 1) = true := by quickRfl
theorem derived_2 : CFSG.KC.RuBA.derivedOK (nat_lit 2) = true := by quickRfl
theorem derived_3 : CFSG.KC.RuBA.derivedOK (nat_lit 3) = true := by quickRfl
theorem derived_4 : CFSG.KC.RuBA.derivedOK (nat_lit 4) = true := by quickRfl
theorem derived_5 : CFSG.KC.RuBA.derivedOK (nat_lit 5) = true := by quickRfl
theorem derived_6 : CFSG.KC.RuBA.derivedOK (nat_lit 6) = true := by quickRfl
theorem derived_7 : CFSG.KC.RuBA.derivedOK (nat_lit 7) = true := by quickRfl
theorem derived_8 : CFSG.KC.RuBA.derivedOK (nat_lit 8) = true := by quickRfl

theorem bot_sub0 : Nat.beq (CFSG.KD.RuBAB.selST (nat_lit 0)) (nat_lit 4) = true := by quickRfl
theorem bot_sub1 : Nat.beq (CFSG.KD.RuBAB.selST (nat_lit 1)) (nat_lit 8196) = true := by quickRfl

theorem bot_p0sq : Nat.beq (CFSG.KD.RuBAB.selRT (nat_lit 0)) (nat_lit 8) = true := by quickRfl
theorem bot_p1sq : Nat.beq (CFSG.KD.RuBAB.selRT (nat_lit 1)) (nat_lit 2105352) = true := by quickRfl
theorem bot_p0p1sq : Nat.beq (CFSG.KD.RuBAB.selRT (nat_lit 4)) (nat_lit 137441050640) = true := by quickRfl

theorem order : Nat.beq (Nat.mul (Nat.mul (Nat.mul CFSG.KD.RuBP.nLive CFSG.KD.RuBAM.nLive) CFSG.KD.RuBAB.nLive) (nat_lit 4))
    (nat_lit 145926144000) = true := by quickRfl

end CFSG.KC.RuBA.Route

end
