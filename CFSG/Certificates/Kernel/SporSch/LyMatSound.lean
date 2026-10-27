module

public import CFSG.Certificates.Kernel.SporSch.LyMatLemmas
public import CFSG.Sporadic.Schreier.LyCheckSylow
import CFSG.Certificates.Kernel.SporSch.LyRunB
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas

public section

namespace CFSG.KS.SporSch.LyM

open CFSG.KC.Ord CFSG.Sporadic.He.Native CFSG.Sporadic.LySchreier.Native

theorem payRunP_eq {p d w S : Nat} (cs : List Char) (hp0 : 0 < p) (hp : p ≤ 2 ^ w)
    (hS : w * d ≤ S) :
    rowsOf p d (String.ofList cs) = unpackL d w S (payRunP p d w S cs 0 0 0) :=
  payRunP_eqL cs hp0 hp hS

theorem mulR_eq {p w S d T L H CM RM ONE LV HV X Y : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true)
    (hX : validM p (d * S) L H X = true) (hY : validM p (d * S) L H Y = true) :
    mulM p d (unpackL d w S X) (unpackL d w S Y) = unpackL d w S (mulR p w S d T L H CM RM X Y) ∧
      validM p (d * S) L H (mulR p w S d T L H CM RM X Y) = true :=
  mulR_eqL hc hX hY

theorem idM_eq {p w S d T L H CM RM ONE LV HV : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) :
    idM d = unpackL d w S ONE ∧ validM p (d * S) L H ONE = true :=
  idM_eqL hc

theorem beq_eq {p w S d T L H CM RM ONE LV HV X Y : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true)
    (hX : validM p (d * S) L H X = true) (hY : validM p (d * S) L H Y = true) :
    (unpackL d w S X == unpackL d w S Y) = Nat.beq X Y :=
  beq_eqL hc hX hY

theorem invM_eq {p w S d T L H CM RM ONE LV HV X Y : Nat} (hpr : p.Prime)
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true)
    (hX : validM p (d * S) L H X = true) (hY : validM p (d * S) L H Y = true)
    (h : Nat.beq (mulR p w S d T L H CM RM X Y) ONE = true) :
    invM p d (unpackL d w S X) = unpackL d w S Y :=
  invM_eqL hpr hc hX hY h

theorem powM_eq {p w S d T L H CM RM ONE LV HV M : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true)
    (hM : validM p (d * S) L H M = true) (e : Nat) :
    powM p d (unpackL d w S M) e = unpackL d w S (powR p w S d T L H CM RM ONE M e) ∧
      validM p (d * S) L H (powR p w S d T L H CM RM ONE M e) = true :=
  powM_eqL hc hM e

theorem wordFromM_eq {w S T L H CM RM ONE LV HV X : Nat} {G GI : Nat → Nat}
    {g gi : Nat → Array (Array Nat)}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hg : ∀ i, g i = unpackL 111 w S (G i) ∧ validM 5 (111 * S) L H (G i) = true)
    (hgi : ∀ i, gi i = unpackL 111 w S (GI i) ∧ validM 5 (111 * S) L H (GI i) = true)
    (hX : validM 5 (111 * S) L H X = true) (ws : List Int) :
    wordFromM g gi (unpackL 111 w S X) ws =
        unpackL 111 w S (wordR 5 w S 111 T L H CM RM G GI X ws) ∧
      validM 5 (111 * S) L H (wordR 5 w S 111 T L H CM RM G GI X ws) = true :=
  wordFromM_eqL hc hg hgi ws X hX

theorem parseK_sound {cs : List Char} {L : List Int} (h : parseK cs L = true) :
    parseInts (String.ofList cs) = L := by
  rw [CFSG.KS.SporSch.LyTxt.parseInts_ofList]
  exact CFSG.KS.SporSch.LyTxt.parseK_pI h

theorem strictN_val (y : Nat) (k : Nat → Nat) : CFSG.KC.Enum.strictN y k = k y := by
  cases y <;> rfl

theorem wordR_append {p w S d T L H CM RM : Nat} {G GI : Nat → Nat} (a b : List Int) (X : Nat) :
    wordR p w S d T L H CM RM G GI X (a ++ b) =
      wordR p w S d T L H CM RM G GI (wordR p w S d T L H CM RM G GI X a) b := by
  induction a generalizing X with
  | nil => rfl
  | cons l a ih =>
    have e1 : ∀ (Y : Nat) (zs : List Int), wordR p w S d T L H CM RM G GI Y (l :: zs) =
        wordR p w S d T L H CM RM G GI (mulR p w S d T L H CM RM Y (letterR G GI l)) zs :=
      fun Y zs => strictN_val (mulR p w S d T L H CM RM Y (letterR G GI l))
        (fun X => wordR p w S d T L H CM RM G GI X zs)
    rw [List.cons_append, e1, e1]
    exact ih _

theorem runB_sound {w S T L H CM RM ONE LV HV kg c cap nS Hh : Nat} {UG E W SO SOI C : Nat → Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hU : ∀ k < kg, validM 5 (111 * S) L H (UG k) = true)
    (hE : ∀ i < c, validM 5 (111 * S) L H (E i) = true) (h0 : E 0 = ONE) (hc512 : c ≤ 512)
    (hsort : ∀ i < c, sortB E SO SOI c i = true)
    (hcap : nS * Hh = cap) (hC0 : C 0 = 1) (hCn : C nS = c)
    (hrun : ∀ q < nS, Nat.beq (runB 5 w S 111 T L H CM RM UG E W kg c Hh (Nat.mul q Hh) (C q))
      (C (Nat.succ q)) = true) {us : Array (Array (Array Nat))}
    (hus : us.size = kg ∧ ∀ k < kg, us[k]! = unpackL 111 w S (UG k)) :
    (sylowBFS us cap).1 =
      Array.ofFn (n := c) fun i => unpackL 111 w S (E i.val) :=
  CFSG.KS.SporSch.LyRB.runB_soundL hc hU hE h0 hc512 hsort hcap hC0 hCn hrun hus

theorem diffMod5_eq {w S T L H CM RM ONE LV HV X Y : Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hX : validM 5 (111 * S) L H X = true) (hY : validM 5 (111 * S) L H Y = true) :
    diffMod5 (unpackL 111 w S X) (unpackL 111 w S Y) = !(Nat.beq X Y) :=
  CFSG.KS.SporSch.LyRB.diffMod5_eqL hc hX hY

end CFSG.KS.SporSch.LyM

end
