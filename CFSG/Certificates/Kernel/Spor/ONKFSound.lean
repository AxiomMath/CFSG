module

public import Certificates.Data.Kernel.Spor.ONKF
public import CFSG.Certificates.Kernel.Spor.ONVecLib
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.ONF

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.F3.Native

def VOk (a : V) : Prop := ∀ i, a.p.testBit i = true → a.m.testBit i = false

private theorem V.ext' {a b : V} (hp : a.p = b.p) (hm : a.m = b.m) : a = b := by
  cases a
  cases b
  simp_all

private theorem add_p_bit (a b : V) (i : Nat) : (a.add b).p.testBit i =
    (((a.p.testBit i ^^ (a.p.testBit i && (b.p.testBit i || b.m.testBit i))) ||
      (b.p.testBit i ^^ (b.p.testBit i && (a.p.testBit i || a.m.testBit i)))) ||
      (a.m.testBit i && b.m.testBit i)) := by
  simp only [V.add, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and]

private theorem add_m_bit (a b : V) (i : Nat) : (a.add b).m.testBit i =
    (((a.m.testBit i ^^ (a.m.testBit i && (b.p.testBit i || b.m.testBit i))) ||
      (b.m.testBit i ^^ (b.m.testBit i && (a.p.testBit i || a.m.testBit i)))) ||
      (a.p.testBit i && b.p.testBit i)) := by
  simp only [V.add, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and]

theorem VOk.add {a b : V} (ha : VOk a) (hb : VOk b) : VOk (a.add b) := fun i => by
  rw [add_p_bit, add_m_bit]
  have h1 := ha i
  have h2 := hb i
  revert h1 h2
  cases a.p.testBit i <;> cases a.m.testBit i <;> cases b.p.testBit i <;> cases b.m.testBit i <;>
    simp

theorem VOk.neg {a : V} (ha : VOk a) : VOk a.neg := fun i h => by
  have := ha i
  cases hp : a.p.testBit i <;> simp_all [V.neg]

theorem VOk.zero : VOk V.zero := fun i => by simp [V.zero]

theorem V.zero_add' (b : V) : V.zero.add b = b :=
  V.ext' (Nat.eq_of_testBit_eq fun i => by rw [add_p_bit]; simp [V.zero])
    (Nat.eq_of_testBit_eq fun i => by rw [add_m_bit]; simp [V.zero])

theorem V.add_zero' (a : V) : a.add V.zero = a :=
  V.ext' (Nat.eq_of_testBit_eq fun i => by rw [add_p_bit]; simp [V.zero])
    (Nat.eq_of_testBit_eq fun i => by rw [add_m_bit]; simp [V.zero])

theorem V.add_assoc' {a b c : V} (ha : VOk a) (hb : VOk b) (hc : VOk c) :
    (a.add b).add c = a.add (b.add c) := by
  apply V.ext'
  · apply Nat.eq_of_testBit_eq
    intro i
    simp only [add_p_bit, add_m_bit]
    have h1 := ha i
    have h2 := hb i
    have h3 := hc i
    revert h1 h2 h3
    cases a.p.testBit i <;> cases a.m.testBit i <;> cases b.p.testBit i <;> cases b.m.testBit i <;>
      cases c.p.testBit i <;> cases c.m.testBit i <;> simp
  · apply Nat.eq_of_testBit_eq
    intro i
    simp only [add_p_bit, add_m_bit]
    have h1 := ha i
    have h2 := hb i
    have h3 := hc i
    revert h1 h2 h3
    cases a.p.testBit i <;> cases a.m.testBit i <;> cases b.p.testBit i <;> cases b.m.testBit i <;>
      cases c.p.testBit i <;> cases c.m.testBit i <;> simp

theorem vOk_canon {c : Nat} (h : canon c = true) : VOk (vOf c) := fun i hp => by
  have h0 := (canon_bits h).1
  have : (vP c &&& vM c).testBit i = false := by rw [h0]; exact Nat.zero_testBit i
  rw [Nat.testBit_and] at this
  change (vP c).testBit i = true at hp
  change (vM c).testBit i = false
  simpa [hp] using this

@[expose] def hiV (a : V) : V := ⟨a.p >>> 64, a.m >>> 64⟩

theorem hiV_add (a b : V) : hiV (a.add b) = (hiV a).add (hiV b) :=
  V.ext' (Nat.eq_of_testBit_eq fun i => by simp [hiV, add_p_bit, Nat.testBit_shiftRight])
    (Nat.eq_of_testBit_eq fun i => by simp [hiV, add_m_bit, Nat.testBit_shiftRight])

@[expose] noncomputable def stepV (c xp xm : Nat) (a : V) : V :=
  if xp.testBit 0 = true then a.add (vOf c) else if xm.testBit 0 = true then a.add (vOf c).neg else a

@[expose] noncomputable def accV : List Nat → Nat → Nat → V → V
  | [], _, _, a => a
  | c :: L, xp, xm, a => accV L (xp >>> 1) (xm >>> 1) (stepV c xp xm a)

private theorem nIfE (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem land_one_beq (y : Nat) : Nat.beq (Nat.land y 1) 1 = y.testBit 0 := by
  change Nat.beq (y &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one y with h | h <;> rw [h] <;> rfl

private theorem mvL_cons' (c : Nat) (L : List Nat) (xp xm ap am : Nat) : mvL (c :: L) xp xm ap am =
    if xp.testBit 0 = true then
      mvL L (xp >>> 1) (xm >>> 1) (addP ap am (vP c) (vM c)) (addM ap am (vP c) (vM c))
    else if xm.testBit 0 = true then
      mvL L (xp >>> 1) (xm >>> 1) (addP ap am (vM c) (vP c)) (addM ap am (vM c) (vP c))
    else mvL L (xp >>> 1) (xm >>> 1) ap am := by
  have e : mvL (c :: L) xp xm ap am = strictN (vP c) fun cp => strictN (vM c) fun cm =>
      nIf(Nat.beq (Nat.land xp (nat_lit 1)) (nat_lit 1),
        strictN (addP ap am cp cm) fun ap' => strictN (addM ap am cp cm) fun am' =>
          mvL L (Nat.shiftRight xp (nat_lit 1)) (Nat.shiftRight xm (nat_lit 1)) ap' am',
        nIf(Nat.beq (Nat.land xm (nat_lit 1)) (nat_lit 1),
          strictN (addP ap am cm cp) fun ap' => strictN (addM ap am cm cp) fun am' =>
            mvL L (Nat.shiftRight xp (nat_lit 1)) (Nat.shiftRight xm (nat_lit 1)) ap' am',
          mvL L (Nat.shiftRight xp (nat_lit 1)) (Nat.shiftRight xm (nat_lit 1)) ap am)) := rfl
  rw [e]
  simp only [PackFld.strictN_eqP, nIfE, land_one_beq]
  rfl

theorem mvL_acc : ∀ (L : List Nat) (xp xm : Nat) (a : V),
    mvL L xp xm a.p a.m = vmk (accV L xp xm a).p (accV L xp xm a).m
  | [], _, _, _ => rfl
  | c :: L, xp, xm, a => by
    rw [mvL_cons']
    simp only [accV, stepV]
    by_cases h1 : xp.testBit 0 = true
    · simp only [h1, if_true]
      exact mvL_acc L _ _ (a.add (vOf c))
    · by_cases h2 : xm.testBit 0 = true
      · simp only [h1, h2, if_true, if_false]
        exact mvL_acc L _ _ (a.add (vOf c).neg)
      · simp only [h1, h2, if_false]
        exact mvL_acc L _ _ a

theorem accV_append : ∀ (L1 L2 : List Nat) (xp xm : Nat) (a : V),
    accV (L1 ++ L2) xp xm a = accV L2 (xp >>> L1.length) (xm >>> L1.length) (accV L1 xp xm a)
  | [], _, _, _, _ => by simp [accV]
  | c :: L, L2, xp, xm, a => by
    simp only [List.cons_append, accV, List.length_cons]
    rw [accV_append L L2, Nat.add_comm L.length 1, Nat.shiftRight_add, Nat.shiftRight_add]

theorem accV_congr : ∀ (L : List Nat) {xp xm yp ym : Nat} (a : V),
    (∀ i < L.length, xp.testBit i = yp.testBit i) → (∀ i < L.length, xm.testBit i = ym.testBit i) →
    accV L xp xm a = accV L yp ym a
  | [], _, _, _, _, _, _, _ => rfl
  | c :: L, xp, xm, yp, ym, a, hp, hm => by
    simp only [accV]
    have e0 : stepV c xp xm a = stepV c yp ym a := by
      simp only [stepV, hp 0 (by simp), hm 0 (by simp)]
    rw [e0]
    exact accV_congr L _ (fun i hi => by
        simpa [Nat.testBit_shiftRight, Nat.add_comm] using hp (i + 1) (by simp; omega))
      (fun i hi => by
        simpa [Nat.testBit_shiftRight, Nat.add_comm] using hm (i + 1) (by simp; omega))

theorem stepV_elim {P : V → Prop} {c xp xm : Nat} {a : V} (h1 : P (a.add (vOf c)))
    (h2 : P (a.add (vOf c).neg)) (h3 : P a) : P (stepV c xp xm a) := by
  unfold stepV
  split
  · exact h1
  · split
    · exact h2
    · exact h3

theorem accV_ok : ∀ (L : List Nat) (xp xm : Nat) {a : V}, VOk a → (∀ c ∈ L, canon c = true) →
    VOk (accV L xp xm a)
  | [], _, _, _, ha, _ => ha
  | c :: L, xp, xm, a, ha, hL => by
    simp only [accV]
    have hc := vOk_canon (hL c List.mem_cons_self)
    exact accV_ok L _ _ (stepV_elim (ha.add hc) (ha.add hc.neg) ha)
      (fun d hd => hL d (List.mem_cons_of_mem c hd))

theorem accV_vb : ∀ (L : List Nat) (xp xm : Nat) {a : V}, VB 256 a → (∀ c ∈ L, canon c = true) →
    VB 256 (accV L xp xm a)
  | [], _, _, _, ha, _ => ha
  | c :: L, xp, xm, a, ha, hL => by
    simp only [accV]
    have hc : VB 256 (vOf c) := fun i hi => vB_canon (hL c List.mem_cons_self) i (by omega)
    exact accV_vb L _ _ (stepV_elim (ha.add hc) (ha.add hc.neg) ha)
      (fun d hd => hL d (List.mem_cons_of_mem c hd))

theorem accV_add : ∀ (L : List Nat) (xp xm : Nat) {a : V}, VOk a → (∀ c ∈ L, canon c = true) →
    accV L xp xm a = a.add (accV L xp xm V.zero)
  | [], _, _, a, _, _ => (V.add_zero' a).symm
  | c :: L, xp, xm, a, ha, hL => by
    have hL' : ∀ d ∈ L, canon d = true := fun d hd => hL d (List.mem_cons_of_mem c hd)
    have hc := vOk_canon (hL c List.mem_cons_self)
    simp only [accV]
    have hs : ∀ b : V, VOk b → VOk (stepV c xp xm b) := fun b hb =>
      stepV_elim (hb.add hc) (hb.add hc.neg) hb
    rw [accV_add L _ _ (hs a ha) hL', accV_add L _ _ (hs _ VOk.zero) hL']
    have hR := accV_ok L (xp >>> 1) (xm >>> 1) VOk.zero hL'
    unfold stepV
    split
    · rw [V.zero_add', V.add_assoc' ha hc hR]
    · split
      · rw [V.zero_add', V.add_assoc' ha hc.neg hR]
      · rw [V.zero_add']

theorem colsOK_spec : ∀ {L : List Nat}, colsOK L = true → ∀ c ∈ L, canon c = true
  | [], _, c, hc => absurd hc List.not_mem_nil
  | d :: L, h, c, hc => by
    have h' : Bool.rec (motive := fun _ => Bool) false (colsOK L) (canon d) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h1
    · exact colsOK_spec h2 c hc

theorem mvFL_succ (T : Nat → Nat) (n c xp xm ap am : Nat) : mvFL T (n + 1) c xp xm ap am =
    mvFL T n (c + 1) (xp >>> 4) (xm >>> 4)
      (V.add ⟨ap, am⟩ ⟨recF T c (xm &&& 15) (xp &&& 15) &&& mask 224,
        recF T c (xm &&& 15) (xp &&& 15) >>> 224⟩).p
      (V.add ⟨ap, am⟩ ⟨recF T c (xm &&& 15) (xp &&& 15) &&& mask 224,
        recF T c (xm &&& 15) (xp &&& 15) >>> 224⟩).m := by
  have e : mvFL T (n + 1) c xp xm ap am =
      strictN (recF T c (Nat.land xm (nat_lit 15)) (Nat.land xp (nat_lit 15))) fun e =>
        strictN (Nat.land e (mask (nat_lit 224))) fun ep => strictN (Nat.shiftRight e (nat_lit 224)) fun em =>
          strictN (addP ap am ep em) fun ap' => strictN (addM ap am ep em) fun am' =>
            mvFL T n (Nat.succ c) (Nat.shiftRight xp (nat_lit 4)) (Nat.shiftRight xm (nat_lit 4)) ap' am' :=
    rfl
  rw [e]
  simp only [PackFld.strictN_eqP]
  try rfl

private theorem mod_bits (x i : Nat) (hi : i < 4) : (x &&& 15).testBit i = x.testBit i := by
  rw [Nat.testBit_and, show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  simp [hi]

private theorem lt_mask224 (e : Nat) : (e &&& mask 224) >>> 64 < 2 ^ 256 := by
  rw [PackFld.mask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have h1 := Nat.mod_lt e (Nat.two_pow_pos 224)
  have h2 : (e % 2 ^ 224) / 2 ^ 64 < 2 ^ 160 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), ← Nat.pow_add]
    exact h1
  exact Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by decide))

theorem recOK_spec {T : Nat → Nat} {c : Nat} {C : List Nat} {xm xp : Nat}
    (h : recOK T c C xm xp = true) (hC : ∀ x ∈ C, canon x = true) :
    hiV ⟨recF T c xm xp &&& mask 224, recF T c xm xp >>> 224⟩ = accV C xp xm V.zero := by
  unfold recOK at h
  simp only [PackFld.strictB_eqP] at h
  have e := (Nat.eq_of_beq_eq_true h).trans (mvL_acc C xp xm V.zero)
  have hb := (accV_vb C xp xm (VB.zero 256) hC).lt.1
  have e3 := congrArg vOf e
  change vOf (vmk ((recF T c xm xp &&& mask 224) >>> 64) ((recF T c xm xp >>> 224) >>> 64)) = _ at e3
  rw [vOf_vmk (lt_mask224 _), vOf_vmk hb] at e3
  exact e3

theorem mvFL_eq {T : Nat → Nat} : ∀ (CS : List (List Nat)) (c xp xm ap am : Nat),
    tabChk T CS c = true → lensOK CS = true → (∀ x ∈ CS.flatten, canon x = true) →
    VOk (hiV ⟨ap, am⟩) →
    mvFL T CS.length c xp xm ap am =
      vmk (accV CS.flatten xp xm (hiV ⟨ap, am⟩)).p (accV CS.flatten xp xm (hiV ⟨ap, am⟩)).m
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | C :: R, c, xp, xm, ap, am, ht, hl, hcol, hok => by
    have ht' : Bool.rec (motive := fun _ => Bool) false (tabChk T R (c + 1))
        (allBlk 0 (fun xm => allBlk 0 (recOK T c C xm) 16) 16) = true := ht
    obtain ⟨ht1, ht2⟩ := (bAnd_iff _ _).1 ht'
    have hl' : Bool.rec (motive := fun _ => Bool) false (lensOK R)
        (List.rec (motive := fun _ => Bool) (Nat.ble C.length 4)
          (fun _ _ _ => Nat.beq C.length 4) R) = true := hl
    obtain ⟨hl1, hl2⟩ := (bAnd_iff _ _).1 hl'
    have hC : ∀ x ∈ C, canon x = true := fun x hx => hcol x (by simp [hx])
    have hR : ∀ x ∈ R.flatten, canon x = true := fun x hx => hcol x (by
      rw [List.flatten_cons]; exact List.mem_append_right _ hx)
    have hlen : C.length ≤ 4 := by
      cases R with
      | nil => exact Nat.le_of_ble_eq_true hl1
      | cons _ _ => exact Nat.le_of_eq (Nat.eq_of_beq_eq_true hl1)
    have hm16 : xm &&& 15 < 16 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have hp16 : xp &&& 15 < 16 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have hrec : recOK T c C (xm &&& 15) (xp &&& 15) = true := by
      have := allBlk_spec ht1 _ hm16
      rw [show Nat.add 0 (xm &&& 15) = xm &&& 15 from Nat.zero_add _] at this
      have := allBlk_spec this _ hp16
      rwa [show Nat.add 0 (xp &&& 15) = xp &&& 15 from Nat.zero_add _] at this
    have hE := recOK_spec hrec hC
    rw [accV_congr C V.zero (fun i hi => mod_bits xp i (by omega))
      (fun i hi => mod_bits xm i (by omega))] at hE
    rw [List.length_cons, mvFL_succ]
    obtain ⟨E, hEd⟩ : ∃ E : V, E = ⟨recF T c (xm &&& 15) (xp &&& 15) &&& mask 224,
      recF T c (xm &&& 15) (xp &&& 15) >>> 224⟩ := ⟨_, rfl⟩
    rw [← hEd]
    rw [← hEd] at hE
    have hA : hiV ⟨(V.add ⟨ap, am⟩ E).p, (V.add ⟨ap, am⟩ E).m⟩ = accV C xp xm (hiV ⟨ap, am⟩) := by
      rw [show (⟨(V.add ⟨ap, am⟩ E).p, (V.add ⟨ap, am⟩ E).m⟩ : V) = V.add ⟨ap, am⟩ E from rfl,
        hiV_add, hE, ← accV_add C xp xm hok hC]
    have hokA : VOk (hiV ⟨(V.add ⟨ap, am⟩ E).p, (V.add ⟨ap, am⟩ E).m⟩) := by
      rw [hA]; exact accV_ok C xp xm hok hC
    rw [mvFL_eq R (c + 1) _ _ _ _ ht2 hl2 hR hokA, hA, List.flatten_cons, accV_append]
    cases R with
    | nil => rfl
    | cons _ _ =>
      rw [Nat.eq_of_beq_eq_true hl1]

theorem mvF_eq {T : Nat → Nat} {CS : List (List Nat)} {L : List Nat} {cnt : Nat}
    (ht : tabChk T CS 0 = true) (hl : lensOK CS = true) (hc : colsOK L = true)
    (hf : (CS.flatten == L) = true) (hn : CS.length = cnt) (X : Nat) : mvF T cnt X = mv L X := by
  have hfl : CS.flatten = L := beq_iff_eq.mp hf
  have hcol := colsOK_spec hc
  have h0 : hiV ⟨0, 0⟩ = V.zero := rfl
  unfold mvF mv
  simp only [PackFld.strictN_eqP]
  subst hn
  refine (mvFL_eq CS 0 (vP X) (vM X) 0 0 ht hl (fun x hx => hcol x (hfl ▸ hx))
    (h0 ▸ VOk.zero)).trans ?_
  rw [hfl, h0]
  exact (mvL_acc L _ _ V.zero).symm

private theorem allBlk_mono {f g : Nat → Bool} (hfg : ∀ i, f i = true → g i = true) (b : Nat) :
    ∀ len, allBlk b f len = true → allBlk b g len = true
  | 0, _ => rfl
  | len + 1, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    show Bool.rec (motive := fun _ => Bool) false (allBlk b g len) (g (Nat.add b len)) = true
    exact (bAnd_iff _ _).2 ⟨hfg _ h1, allBlk_mono hfg b len h2⟩

theorem mvRangeF_imp {K TA TB A B : Nat → Nat} {CA CB : List (List Nat)} {LA LB : List Nat}
    {cnt n lo len : Nat}
    (htA : tabChk TA CA 0 = true) (hlA : lensOK CA = true) (hcA : colsOK LA = true)
    (hfA : (CA.flatten == LA) = true) (hnA : CA.length = cnt)
    (htB : tabChk TB CB 0 = true) (hlB : lensOK CB = true) (hcB : colsOK LB = true)
    (hfB : (CB.flatten == LB) = true) (hnB : CB.length = cnt)
    (h : mvRangeF K TA TB cnt A B n lo len = true) : mvRange K LA LB A B n lo len = true := by
  refine allBlk_mono (fun i hi => ?_) lo len h
  have e : mvAtF K TA TB cnt A B n i = mvAt K LA LB A B n i := by
    simp only [mvAtF, mvAt, mvF_eq htA hlA hcA hfA hnA, mvF_eq htB hlB hcB hfB hnB]
  rwa [← e]

end CFSG.KS.ONF
