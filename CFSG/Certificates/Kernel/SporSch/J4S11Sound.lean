module

public import Certificates.Data.Kernel.SporSch.J4S11
public import CFSG.Certificates.Kernel.SporSch.J4SPairSound
public import CFSG.Sporadic.Schreier.J4SElevenData
import CFSG.Certificates.Kernel.SporSch.J4S11.Parse
import CFSG.Certificates.Kernel.SporSch.J4S11.Pow
import CFSG.Certificates.Kernel.SporSch.J4S11.Dist
import CFSG.Certificates.Kernel.SporSch.J4S11.Fix

public section

namespace CFSG.KS.SporSch.J4E

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KS.SporSch.J4B CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ
open CFSG.SectionRank.Native CFSG.Sporadic.SmallF2.Native

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

theorem parseK_sound {cs : List Char} {codes : List (List Nat)} (h : parseK cs = some codes) :
    (parseSLP (String.ofList cs)).map (List.map instrCode) = some codes := by
  exact ParsePf.parseK_sound' h

theorem decodeK_code (ins : Instr) : decodeK (instrCode ins) = ins := by
  cases ins <;> rfl

theorem strictN_eq₃ (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem beq_false₃ {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

variable (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6)
include hK

theorem powB_enc : ∀ (fuel e : Nat) {X : Array Nat}, WfN X → e < 2 ^ fuel →
    WfN (O.pow X e) ∧ encN (O.pow X e) = powBJ c rm one fuel (encN X) e
  | 0, e, X, _, he => by
    have he0 : e = 0 := by simpa using he
    subst he0
    rw [Ops.pow, ite_eq_left rfl]
    exact ⟨(J4B.id_enc hK).1, (J4B.id_enc hK).2⟩
  | fuel + 1, e, X, hX, he => by
    have hb : powBJ c rm one (fuel + 1) (encN X) e =
        nIf(Nat.beq e (nat_lit 0), one, nIf(Nat.beq e (nat_lit 1), encN X,
          strictN (powBJ c rm one fuel (mulJ c rm (encN X) (encN X)) (Nat.div e (nat_lit 2)))
            fun Y => nIf(Nat.beq (Nat.mod e (nat_lit 2)) (nat_lit 1), mulJ c rm (encN X) Y, Y))) :=
      rfl
    rw [hb, Ops.pow]
    by_cases he0 : e = 0
    · subst he0
      rw [ite_eq_left rfl]
      exact ⟨(J4B.id_enc hK).1, (J4B.id_enc hK).2⟩
    have hb0 : Nat.beq e 0 = false := beq_false₃ he0
    rw [ite_eq_right he0, hb0]
    by_cases he1 : e = 1
    · subst he1
      rw [ite_eq_left rfl]
      exact ⟨hX, rfl⟩
    have hb1 : Nat.beq e 1 = false := beq_false₃ he1
    rw [ite_eq_right he1, hb1]
    have mXX := J4B.mul_enc hK hX hX
    have ih := powB_enc fuel (e / 2) mXX.1 (by rw [pow_succ] at he; omega)
    rw [← mXX.2, strictN_eq₃]
    change WfN (if e % 2 = 1 then O.mul X (O.pow (O.mul X X) (e / 2)) else O.pow (O.mul X X) (e / 2)) ∧
      encN (if e % 2 = 1 then O.mul X (O.pow (O.mul X X) (e / 2)) else O.pow (O.mul X X) (e / 2)) =
      nIf(Nat.beq (e % 2) 1, mulJ c rm (encN X) (powBJ c rm one fuel (encN (O.mul X X)) (e / 2)),
        powBJ c rm one fuel (encN (O.mul X X)) (e / 2))
    by_cases hm : e % 2 = 1
    · have hb2 : Nat.beq (e % 2) 1 = true := by rw [hm]; rfl
      rw [if_pos hm, hb2]
      have m := J4B.mul_enc hK hX ih.1
      exact ⟨m.1, by rw [m.2, ih.2]⟩
    · rw [if_neg hm, beq_false₃ hm]
      exact ih

theorem powP_okB {P : Pair} {a b : Nat} (hP : PairOK P a b) {fuel e : Nat} (he : e < 2 ^ fuel) :
    PairOK (powP P e) (powBJ c rm one fuel a e) (powBJ c rm one fuel b e) := by
  have m1 := powB_enc hK fuel e hP.1.1 he
  have m2 := powB_enc hK fuel e hP.2.1 he
  exact ⟨⟨m1.1, m1.2.trans (by rw [hP.1.2])⟩, ⟨m2.1, m2.2.trans (by rw [hP.2.2])⟩⟩

theorem eq_sound {X Y U V : Array Nat} (hX : WfN X) (hY : WfN Y) (hU : WfN U) (hV : WfN V)
    (h : Nat.beq (mulJ c rm (encN X) (encN Y)) (mulJ c rm (encN U) (encN V)) = true) :
    O.eq (O.mul X Y) (O.mul U V) = true := by
  have m1 := J4B.mul_enc hK hX hY
  have m2 := J4B.mul_enc hK hU hV
  have e : O.mul X Y = O.mul U V :=
    J4B.enc_inj m1.1 m2.1 (by rw [m1.2, m2.2]; exact Nat.eq_of_beq_eq_true h)
  change (O.mul X Y == O.mul U V) = true
  rw [e]
  exact beq_self_eq_true _

theorem eq_one_sound {X Y : Array Nat} (hX : WfN X) (hY : WfN Y)
    (h : Nat.beq (mulJ c rm (encN X) (encN Y)) one = true) : O.eq (O.mul X Y) O.one = true := by
  have m := J4B.mul_enc hK hX hY
  have i := J4B.id_enc hK
  have e : O.mul X Y = idRows 112 :=
    J4B.enc_inj m.1 i.1 (by rw [m.2, i.2]; exact Nat.eq_of_beq_eq_true h)
  change (O.mul X Y == idRows 112) = true
  rw [e]
  exact beq_self_eq_true _

theorem pow_one_sound {X : Array Nat} (hX : WfN X) {e : Nat}
    (h : Nat.beq (powJ c rm one (encN X) e) one = true) : O.eq (O.pow X e) O.one = true := by
  have m := pow_enc hK hX e
  have i := J4B.id_enc hK
  have e' : O.pow X e = idRows 112 :=
    J4B.enc_inj m.1 i.1 (by rw [m.2, i.2]; exact Nat.eq_of_beq_eq_true h)
  change (O.pow X e == idRows 112) = true
  rw [e']
  exact beq_self_eq_true _

theorem expK_sound {X Y Z : Array Nat} (hX : WfN X) (hY : WfN Y) (hZ : WfN Z)
    (h : expK c rm one (encN X) (encN Y) (encN Z) = true) : expOK X Y Z = true := by
  exact PowPf.expK_sound' hK hX hY hZ h

theorem centerK_sound {X Y : Array Nat} (hX : WfN X) (hY : WfN Y)
    (h : centerK c rm one (encN X) (encN Y) = true) : centerOK X Y = true := by
  exact PowPf.centerK_sound' hK hX hY h

theorem distK_sound {X Y Z : Array Nat} (hX : WfN X) (hY : WfN Y) (hZ : WfN Z)
    (h : distK rm 11 [encN X, encN Y, encN Z] 1331 = true) :
    O.normalFormOK 11 [X, Y, Z] 0 = true := by
  exact DistPf.distK_sound' hK hX hY hZ h

theorem sixteenK_sound {U W : Array Nat} (hU : WfN U) (hW : WfN W)
    (h : distK rm 8 [encN U, encN W] 16 = true) : sixteenOK U W = true := by
  exact DistPf.sixteenK_sound' hK hU hW h

theorem fixK_sound {G P Pi R : Array Nat} (hG : WfN G) (hP : WfN P) (hPi : WfN Pi) (hR : WfN R)
    {k : Nat} (hk : k ≤ 112)
    (h : fixK c rm one (encN G) (encN P) (encN Pi) (encN R) k = true) :
    fixDimOK G P Pi R k = true := by
  exact FixPf.fixK_sound' hK hG hP hPi hR hk h

theorem vne_sound {Z : Array Nat} (hZ : WfN Z)
    (h : notB (Nat.beq (vecJ rm (nat_lit 1) (encN Z)) (nat_lit 1)) = true) :
    O.vne (O.vmul (O.unit 0) Z) (O.unit 0) = true := by
  exact PowPf.vne_sound' hK hZ h

omit hK

theorem run_agree : ∀ (p : List Instr) (R S : Array Pair), (∀ ins ∈ p, ins.lt 7 = true) →
    7 ≤ R.size → S.size = 7 → (∀ r < 7, R[r]! = S[r]!) →
    ∀ r < 7, (runProgN O R p)[r]! = (runProgN O S p)[r]!
  | [], R, S, _, _, _, h => h
  | ins :: p, R, S, hp, hR, hS, h => by
    have hi := hp ins List.mem_cons_self
    have hr : ∀ {k : Nat} (v : Pair), k < 7 → ∀ r < 7,
        (R.setIfInBounds k v)[r]! = (S.setIfInBounds k v)[r]! := by
      intro k v hk r hr
      rw [get_set (by omega) (by omega), get_set (by omega) (by omega), h r hr]
    have hstep : (∀ r < 7, (Instr.runN O R ins)[r]! = (Instr.runN O S ins)[r]!) ∧
        7 ≤ (Instr.runN O R ins).size ∧ (Instr.runN O S ins).size = 7 := by
      cases ins with
      | mu i j k =>
        simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hi
        obtain ⟨⟨hi, hj⟩, hk⟩ := hi
        simp only [Instr.runN, Array.size_setIfInBounds, h i hi, h j hj]
        exact ⟨hr _ hk, hR, hS⟩
      | iv i k =>
        simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hi
        obtain ⟨hi, hk⟩ := hi
        simp only [Instr.runN, Array.size_setIfInBounds, h i hi]
        exact ⟨hr _ hk, hR, hS⟩
      | pwr e i k =>
        simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hi
        obtain ⟨hi, hk⟩ := hi
        simp only [Instr.runN, Array.size_setIfInBounds, h i hi]
        exact ⟨hr _ hk, hR, hS⟩
    have ih := run_agree p _ _ (fun i hi => hp i (List.mem_cons_of_mem _ hi)) hstep.2.1 hstep.2.2
      hstep.1
    simpa only [runProgN, List.foldl_cons] using ih

end CFSG.KS.SporSch.J4E

end
