module

public import Certificates.Data.Kernel.GHarrisFus.Tab
public import Certificates.Data.Kernel.GHarrisFus.Cls
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusSound

public section

namespace CFSG.KC.GHFus

open CFSG.ComponentClassification.GHarris.SCert

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : CFSG.KC.Enum.strictN y k = k y := by
  cases y <;> rfl

theorem band' (a b : Bool) : Bool.and' a b = (a && b) := by cases a <;> cases b <;> rfl

theorem bor' (a b : Bool) : Bool.or' a b = (a || b) := by cases a <;> cases b <;> rfl

theorem bnot' (a : Bool) : Bool.not' a = !a := by cases a <;> rfl

theorem allBelow_spec {n : Nat} {p : Nat → Bool} (h : allBelow n p = true) : ∀ i < n, p i = true := by
  induction n with
  | zero => exact fun i hi => absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    have h' : Bool.and' (p n) (allBelow n p) = true := h
    rw [band', Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih h'.2 i hi
    · exact h'.1

@[expose] noncomputable def dmN (x y : Nat) : Nat := (dmP >>> ((8 * x + y) <<< 2)) &&& 15

@[expose] def addS (x y : Nat) : Nat :=
  16 * ((x / 16 + y / 16) % 4) + 4 * ((x / 4 % 4 + y / 4 % 4) % 4) + (x % 4 + y % 4) % 4

theorem mulK_eq (dm mv a b : Nat) : mulK dm mv a b =
    ((dm >>> ((a >>> 6) <<< 5 ||| (b >>> 6) <<< 2)) &&& 7) <<< 6 |||
      addV (a &&& 63) ((mv >>> (((a &&& 448) ||| (b &&& 63)) <<< 3)) &&& 63) := rfl

theorem rowN_eq (d i w : Nat) : rowN d i w =
    (meN d i 0 * ((w >>> 4) &&& 3) + meN d i 1 * ((w >>> 2) &&& 3) + meN d i 2 * (w &&& 3)) % 4 :=
  rfl

theorem mvN_eq (d w : Nat) : mvN d w = 16 * rowN d 0 w + 4 * rowN d 1 w + rowN d 2 w := rfl

theorem rowN_lt (d i w : Nat) : rowN d i w < 4 := Nat.mod_lt _ (by decide)

theorem mvN_lt (d w : Nat) : mvN d w < 64 := by
  have h0 := rowN_lt d 0 w
  have h1 := rowN_lt d 1 w
  have h2 := rowN_lt d 2 w
  rw [mvN_eq]
  omega

theorem addS_lt (x y : Nat) : addS x y < 64 := by
  unfold addS
  omega

theorem fin512 : allBelow 512 (fun i => Nat.beq (i >>> 6) (i / 64) && Nat.beq (i &&& 63) (i % 64) &&
    Nat.beq (i &&& 448) (i / 64 * 64) && Nat.beq (i / 64 * 64 ||| i % 64) (i / 64 * 64 + i % 64)) =
    true := by
  decide +kernel

theorem fin64 : allBelow 64 (fun i => Nat.beq ((i / 8) <<< 5 ||| (i % 8) <<< 2) (i <<< 2) &&
    Nat.beq ((i >>> 4) &&& 3) (i / 16) && Nat.beq ((i >>> 2) &&& 3) (i / 4 % 4) &&
    Nat.beq (i &&& 3) (i % 4)) = true := by
  decide +kernel

theorem fin4096 : allBelow 4096 (fun i => Nat.beq (addV (i / 64) (i % 64)) (addS (i / 64) (i % 64))) =
    true := by
  decide +kernel

theorem bits512 {i : Nat} (hi : i < 512) : i >>> 6 = i / 64 ∧ i &&& 63 = i % 64 ∧
    i &&& 448 = i / 64 * 64 ∧ (i / 64 * 64 ||| i % 64) = i / 64 * 64 + i % 64 := by
  have h := allBelow_spec fin512 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem bits64 {i : Nat} (hi : i < 64) : ((i / 8) <<< 5 ||| (i % 8) <<< 2) = i <<< 2 ∧
    (i >>> 4) &&& 3 = i / 16 ∧ (i >>> 2) &&& 3 = i / 4 % 4 ∧ i &&& 3 = i % 4 := by
  have h := allBelow_spec fin64 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem addV_eq {x y : Nat} (hx : x < 64) (hy : y < 64) : addV x y = addS x y := by
  have h := Nat.eq_of_beq_eq_true (allBelow_spec fin4096 (64 * x + y) (by omega))
  rwa [show (64 * x + y) / 64 = x by omega, show (64 * x + y) % 64 = y by omega] at h

theorem mulK_spec {dm mv : Nat} (hdm : dmOK dm = true) (hmv : mvOK mv = true) {a b : Nat}
    (ha : a < 512) (hb : b < 512) :
    mulK dm mv a b = 64 * dmN (a / 64) (b / 64) + addS (a % 64) (mvN (a / 64) (b % 64)) := by
  obtain ⟨a1, a2, a3, -⟩ := bits512 ha
  obtain ⟨b1, b2, -, -⟩ := bits512 hb
  have hi : 8 * (a / 64) + b / 64 < 64 := by omega
  have i1 := (bits64 hi).1
  rw [show (8 * (a / 64) + b / 64) / 8 = a / 64 by omega,
    show (8 * (a / 64) + b / 64) % 8 = b / 64 by omega] at i1
  have hj : a / 64 * 64 + b % 64 < 512 := by omega
  have j4 := (bits512 hj).2.2.2
  rw [show (a / 64 * 64 + b % 64) / 64 = a / 64 by omega,
    show (a / 64 * 64 + b % 64) % 64 = b % 64 by omega] at j4
  have hD : (dm >>> ((8 * (a / 64) + b / 64) <<< 2)) &&& 7 = dmN (a / 64) (b / 64) :=
    Nat.eq_of_beq_eq_true (allBelow_spec hdm _ hi)
  have hM : (mv >>> ((a / 64 * 64 + b % 64) <<< 3)) &&& 63 =
      mvN ((a / 64 * 64 + b % 64) >>> 6) ((a / 64 * 64 + b % 64) &&& 63) :=
    Nat.eq_of_beq_eq_true (allBelow_spec hmv _ hj)
  rw [(bits512 hj).1, (bits512 hj).2.1, show (a / 64 * 64 + b % 64) / 64 = a / 64 by omega,
    show (a / 64 * 64 + b % 64) % 64 = b % 64 by omega] at hM
  rw [mulK_eq, a1, b1, i1, hD, a3, b2, j4, hM, a2,
    addV_eq (Nat.mod_lt _ (by decide)) (mvN_lt _ _),
    ← Nat.shiftLeft_add_eq_or_of_lt (addS_lt _ _ : _ < 2 ^ 6), Nat.shiftLeft_eq]
  omega

theorem dmN_dmul : ∀ x y : Fin 8, dmN x.val y.val = (dmul x y).val := by decide

theorem meN_me : ∀ (d : Fin 8) (i k : Fin 3), meN d.val i.val k.val = (me d i k).val := by decide

theorem enc_parts (s : SE) : s.enc / 64 = s.d.val ∧ s.enc % 64 / 16 = s.v0.val ∧
    s.enc % 64 / 4 % 4 = s.v1.val ∧ s.enc % 64 % 4 = s.v2.val := by
  have := s.d.isLt
  have := ZMod.val_lt s.v0
  have := ZMod.val_lt s.v1
  have := ZMod.val_lt s.v2
  unfold SE.enc
  omega

theorem zval4 (x y1 y2 y3 z1 z2 z3 : ZMod 4) :
    (x + (y1 * z1 + y2 * z2 + y3 * z3)).val =
      (x.val + y1.val * z1.val + y2.val * z2.val + y3.val * z3.val) % 4 := by
  rw [← ZMod.val_natCast (n := 4) (x.val + y1.val * z1.val + y2.val * z2.val + y3.val * z3.val)]
  congr 1
  push_cast
  simp only [ZMod.natCast_zmod_val]
  ring

theorem mvN_enc (d : Fin 8) (b : SE) : mvN d.val (b.enc % 64) =
    16 * (((me d 0 0).val * b.v0.val + (me d 0 1).val * b.v1.val + (me d 0 2).val * b.v2.val) % 4) +
    4 * (((me d 1 0).val * b.v0.val + (me d 1 1).val * b.v1.val + (me d 1 2).val * b.v2.val) % 4) +
    ((me d 2 0).val * b.v0.val + (me d 2 1).val * b.v1.val + (me d 2 2).val * b.v2.val) % 4 := by
  obtain ⟨-, e0, e1, e2⟩ := enc_parts b
  obtain ⟨-, w1, w2, w3⟩ := bits64 (Nat.mod_lt b.enc (by decide : 0 < 64))
  have m00 : meN d.val 0 0 = (me d 0 0).val := meN_me d 0 0
  have m01 : meN d.val 0 1 = (me d 0 1).val := meN_me d 0 1
  have m02 : meN d.val 0 2 = (me d 0 2).val := meN_me d 0 2
  have m10 : meN d.val 1 0 = (me d 1 0).val := meN_me d 1 0
  have m11 : meN d.val 1 1 = (me d 1 1).val := meN_me d 1 1
  have m12 : meN d.val 1 2 = (me d 1 2).val := meN_me d 1 2
  have m20 : meN d.val 2 0 = (me d 2 0).val := meN_me d 2 0
  have m21 : meN d.val 2 1 = (me d 2 1).val := meN_me d 2 1
  have m22 : meN d.val 2 2 = (me d 2 2).val := meN_me d 2 2
  rw [mvN_eq, rowN_eq, rowN_eq, rowN_eq, w1, w2, w3, e0, e1, e2, m00, m01, m02, m10, m11, m12, m20,
    m21, m22]

theorem mulS_enc (a b : SE) :
    64 * dmN (a.enc / 64) (b.enc / 64) + addS (a.enc % 64) (mvN (a.enc / 64) (b.enc % 64)) =
      (a * b).enc := by
  obtain ⟨ad, a0, a1, a2⟩ := enc_parts a
  obtain ⟨bd, -, -, -⟩ := enc_parts b
  have L : (a * b).enc = (dmul a.d b.d).val * 64 +
      (a.v0 + (me a.d 0 0 * b.v0 + me a.d 0 1 * b.v1 + me a.d 0 2 * b.v2)).val * 16 +
      (a.v1 + (me a.d 1 0 * b.v0 + me a.d 1 1 * b.v1 + me a.d 1 2 * b.v2)).val * 4 +
      (a.v2 + (me a.d 2 0 * b.v0 + me a.d 2 1 * b.v1 + me a.d 2 2 * b.v2)).val := rfl
  rw [ad, bd, dmN_dmul, mvN_enc, L, zval4, zval4, zval4]
  unfold addS
  rw [a0, a1, a2]
  generalize (me a.d 0 0).val * b.v0.val = p00
  generalize (me a.d 0 1).val * b.v1.val = p01
  generalize (me a.d 0 2).val * b.v2.val = p02
  generalize (me a.d 1 0).val * b.v0.val = p10
  generalize (me a.d 1 1).val * b.v1.val = p11
  generalize (me a.d 1 2).val * b.v2.val = p12
  generalize (me a.d 2 0).val * b.v0.val = p20
  generalize (me a.d 2 1).val * b.v1.val = p21
  generalize (me a.d 2 2).val * b.v2.val = p22
  omega

theorem mulK_enc {dm mv : Nat} (hdm : dmOK dm = true) (hmv : mvOK mv = true) (a b : SE) :
    mulK dm mv a.enc b.enc = (a * b).enc := by
  rw [mulK_spec hdm hmv (SE.enc_lt a) (SE.enc_lt b), mulS_enc]

theorem ctFrom_spec (CT : Nat) (l : List Nat) :
    ∀ j, ctFrom CT l j = true → ∀ n (h : n < l.length), clsK CT (j + n) = l[n] := by
  induction l with
  | nil => exact fun _ _ n h => absurd h (Nat.not_lt_zero n)
  | cons x l ih =>
    intro j hj n hn
    have h' : Bool.and' (Nat.beq (clsK CT j) x)
        (CFSG.KC.Enum.strictB (Nat.succ j) (ctFrom CT l)) = true := hj
    rw [band', strictB_eq', Bool.and_eq_true] at h'
    cases n with
    | zero => exact Nat.eq_of_beq_eq_true h'.1
    | succ n =>
      have := ih (Nat.succ j) h'.2 n (by simpa using hn)
      rw [show j + (n + 1) = Nat.succ j + n by omega]
      exact this

theorem clsK_enc {CT : Nat} (hCT : ctOK CT (Array.toList SE.clsArr) = true) (s : SE) :
    clsK CT s.enc = SE.clsTab s := by
  have hs : s.enc < SE.clsArr.size := by
    have := SE.enc_lt s
    have e : SE.clsArr.size = 512 := by decide +kernel
    omega
  have := ctFrom_spec CT _ 0 hCT s.enc (by simpa using hs)
  rw [Nat.zero_add] at this
  rw [this, SE.clsTab, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs, Option.getD_some,
    Array.getElem_toList]

@[expose] noncomputable def walkRF (f : Nat → Nat → Bool) (lo hi : Nat) (L : List (Nat × Nat)) :
    Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun e _ ih j m => Bool.and'
      (Bool.or' (Bool.not' (Bool.and' (Nat.beq (Nat.land m (nat_lit 1)) (nat_lit 1))
          (Bool.and' (Nat.ble lo j) (Nat.blt j hi))))
        (Prod.rec (motive := fun _ => Bool) f e))
      (CFSG.KC.Enum.strictB (Nat.succ j) fun j' =>
        CFSG.KC.Enum.strictB (Nat.shiftRight m (nat_lit 1)) (ih j'))) L

theorem walkRF_cons (f : Nat → Nat → Bool) (lo hi a b : Nat) (L : List (Nat × Nat)) (j m : Nat) :
    walkRF f lo hi ((a, b) :: L) j m = true ↔
      ((m % 2 = 1 → lo ≤ j → j < hi → f a b = true) ∧ walkRF f lo hi L (j + 1) (m / 2) = true) := by
  change Bool.and' _ (CFSG.KC.Enum.strictB (Nat.succ j) fun j' =>
    CFSG.KC.Enum.strictB (Nat.shiftRight m 1) (walkRF f lo hi L j')) = true ↔ _
  rw [strictB_eq', strictB_eq', band', bor', bnot', band', band', Bool.and_eq_true]
  have e1 : Nat.land m 1 = m % 2 := Nat.and_one_is_mod m
  have e2 : Nat.shiftRight m 1 = m / 2 := by
    change m >>> 1 = m / 2
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have ep : Prod.rec (motive := fun _ => Bool) f (a, b) = f a b := rfl
  rw [e1, e2, ep]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun hm hl hh => ?_, h2⟩
    have : (Nat.beq (m % 2) 1 && (Nat.ble lo j && Nat.blt j hi)) = true := by
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq]
      exact ⟨hm, hl, hh⟩
    rw [this, Bool.not_true, Bool.false_or] at h1
    exact h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    cases hf : f a b
    · cases hb : (Nat.beq (m % 2) 1 && (Nat.ble lo j && Nat.blt j hi))
      · rfl
      · simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq] at hb
        rw [h1 hb.1 hb.2.1 hb.2.2] at hf
        exact absurd hf (by decide)
    · exact Bool.or_true _

theorem walkRF_iff (f : Nat → Nat → Bool) (lo hi : Nat) (L : List (Nat × Nat)) :
    ∀ j m, walkRF f lo hi L j m = true ↔ ∀ n (h : n < L.length), m.testBit n = true →
      lo ≤ j + n → j + n < hi → f L[n].1 L[n].2 = true := by
  induction L with
  | nil => exact fun j m => ⟨fun _ n h => absurd h (Nat.not_lt_zero n), fun _ => rfl⟩
  | cons e L ih =>
    obtain ⟨a, b⟩ := e
    intro j m
    rw [walkRF_cons, ih]
    constructor
    · rintro ⟨h0, hr⟩ n hn hb hl hh
      cases n with
      | zero =>
        rw [Nat.testBit_zero, decide_eq_true_eq] at hb
        exact h0 hb (by omega) (by omega)
      | succ n =>
        rw [Nat.testBit_add_one] at hb
        exact hr n (by simpa using hn) hb (by omega) (by omega)
    · intro h
      refine ⟨fun hm hl hh => ?_, fun n hn hb hl hh => ?_⟩
      · have := h 0 (by simp) (by rw [Nat.testBit_zero, decide_eq_true_eq]; exact hm) (by omega)
          (by omega)
        exact this
      · have := h (n + 1) (by simpa using hn) (by rw [Nat.testBit_add_one]; exact hb) (by omega)
          (by omega)
        exact this

theorem fusRange_eq (dm mv CT : Nat) (L : List (Nat × Nat)) (v P : Nat) (t1 t2 t3 : Test)
    (IK : List (Nat × List Nat)) (BP : Nat) (EW : List (Nat × List Nat)) (zw : List Nat)
    (uE uF : Bool) (good : Nat → Bool) (lo hi : Nat) :
    fusRange dm mv CT L (v, P, (t1, t2, t3), IK, BP, EW, zw, uE, uF) good lo hi =
      walkRF (stage1 dm mv CT BP v (rowK dm mv v L) P L t1 t2 t3 IK EW zw uE uF good) lo hi L 0
        (lane (rowK dm mv v L) (nib P 0)) := by
  change CFSG.KC.Enum.strictB (rowK dm mv v L) (fun Rv =>
    walkR (stage1 dm mv CT BP v Rv P L t1 t2 t3 IK EW zw uE uF good) lo hi L (lane Rv (nib P 0))) = _
  rw [strictB_eq']
  rfl

theorem fusRange_append {dm mv CT : Nat} {L : List (Nat × Nat)} {D : FusT} {good : Nat → Bool}
    {lo mid hi : Nat} (h1 : fusRange dm mv CT L D good lo mid = true)
    (h2 : fusRange dm mv CT L D good mid hi = true) : fusRange dm mv CT L D good lo hi = true := by
  obtain ⟨v, P, ⟨t1, t2, t3⟩, IK, BP, EW, zw, uE, uF⟩ := D
  rw [fusRange_eq, walkRF_iff] at h1 h2 ⊢
  intro n hn hb hl hh
  by_cases hm : 0 + n < mid
  · exact h1 n hn hb hl hm
  · exact h2 n hn hb (by omega) hh

@[expose] def FusHyp (A : Fus.Data) : Prop :=
  ∀ q1 q2 q3 : SE, Fus.isInv (· * ·) q1 = true → Fus.isInv (· * ·) q2 = true →
    Fus.isInv (· * ·) q3 = true → A.pairOk (· * ·) #[A.target, q1, 1, 1] 0 1 = true →
    A.pairOk (· * ·) #[A.target, q1, q2, 1] 0 2 = true →
    A.pairOk (· * ·) #[A.target, q1, q2, 1] 1 2 = true →
    A.pairOk (· * ·) #[A.target, q1, q2, q3] 0 3 = true →
    A.pairOk (· * ·) #[A.target, q1, q2, q3] 1 3 = true →
    A.pairOk (· * ·) #[A.target, q1, q2, q3] 2 3 = true →
    A.condB (· * ·) #[A.target, q1, q2, q3] = true → A.outB (· * ·) #[A.target, q1, q2, q3] = true

theorem checkM_of {A : Fus.Data} (ht : A.tableOk (· * ·) = true) (h : FusHyp A) :
    A.checkM (· * ·) = true := by
  unfold Fus.Data.checkM
  rw [ht, Bool.true_and, List.all_eq_true]
  intro q1 hq1
  have i1 := (List.mem_filter.mp hq1).2
  cases e01 : A.pairOk (· * ·) #[A.target, q1, 1, 1] 0 1
  · rfl
  rw [Bool.not_true, Bool.false_or, List.all_eq_true]
  intro q2 hq2
  have i2 := (List.mem_filter.mp hq2).2
  cases e02 : A.pairOk (· * ·) #[A.target, q1, q2, 1] 0 2
  · rfl
  cases e12 : A.pairOk (· * ·) #[A.target, q1, q2, 1] 1 2
  · rfl
  rw [Bool.and_self, Bool.not_true, Bool.false_or, List.all_eq_true]
  intro q3 hq3
  have i3 := (List.mem_filter.mp hq3).2
  cases e03 : A.pairOk (· * ·) #[A.target, q1, q2, q3] 0 3
  · rfl
  cases e13 : A.pairOk (· * ·) #[A.target, q1, q2, q3] 1 3
  · rfl
  cases e23 : A.pairOk (· * ·) #[A.target, q1, q2, q3] 2 3
  · rfl
  cases ec : A.condB (· * ·) #[A.target, q1, q2, q3]
  · rfl
  rw [h q1 q2 q3 i1 i2 i3 e01 e02 e12 e03 e13 e23 ec]
  rfl

@[expose] def patCode (x y : SE) : Nat :=
  (x * y == 1).toNat + 2 * ((x * y) * (x * y) == 1).toNat +
    4 * ((x * y) * (x * y) * ((x * y) * (x * y)) == 1).toNat + 8 * (x * y == y * x).toNat

@[expose] def walkIdx (A : Fus.Data) (w : List Nat) : Nat := w.foldl (fun k i => A.mi k (i / 9)) 0

@[expose] def TestRel (A : Fus.Data) (t : Test) : Prop :=
  (∀ i ∈ t.1, i = 0 ∨ i = 9 ∨ i = 18) ∧ (∀ i ∈ t.2.1, i = 0 ∨ i = 9 ∨ i = 18 ∨ i = 27) ∧
    (walkIdx A (t.1 ++ t.2.1) == 0) = t.2.2

@[expose] def word9 (A : Fus.Data) (k : Nat) : List Nat := (A.words.getD k []).map (9 * ·)

@[expose] def FusRel (A : Fus.Data) (D : FusT) : Prop :=
  D.1 = A.target.enc ∧
  (∀ k < 6, nib D.2.1 k = patCode (A.gens.getD ([0, 0, 1, 0, 1, 2].getD k 0) 1)
    (A.gens.getD ([1, 2, 2, 3, 3, 3].getD k 0) 1)) ∧
  TestRel A D.2.2.1.1 ∧ TestRel A D.2.2.1.2.1 ∧ TestRel A D.2.2.1.2.2 ∧
  D.2.2.2.1 = ((List.range 32).filter fun k => Fus.isInv (· * ·) (A.elt (· * ·) k)).map
    (fun k => (9 * SE.clsTab (A.elt (· * ·) k), word9 A k)) ∧
  (∀ i < 9, ∀ j < 9, D.2.2.2.2.1.testBit (9 * i + j) = true → (i, j) ∈ A.badPairs) ∧
  D.2.2.2.2.2.1 = (List.range 32).map (fun k => ((A.elt (· * ·) k).enc, word9 A k)) ∧
  D.2.2.2.2.2.2.1 = word9 A A.zIdx ∧ D.2.2.2.2.2.2.2.1 = A.useE ∧ D.2.2.2.2.2.2.2.2 = A.useF

@[expose] def pack (v q1 q2 q3 : SE) : Nat :=
  Nat.lor (Nat.lor (Nat.lor v.enc (Nat.shiftLeft q1.enc 9)) (Nat.shiftLeft q2.enc 18))
    (Nat.shiftLeft q3.enc 27)

theorem enc_inj {a b : SE} (h : a.enc = b.enc) : a = b := by
  rw [← SE.dec_enc a, ← SE.dec_enc b, h]

theorem nbeq_enc (a b : SE) : Nat.beq a.enc b.enc = (a == b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]
  exact ⟨enc_inj, fun h => h ▸ rfl⟩

theorem nbeq0_enc (a : SE) : Nat.beq a.enc 0 = (a == 1) := nbeq_enc a 1

theorem bits4 (b0 b1 b2 b3 : Bool) :
    Nat.lor (Nat.lor b0.toNat (Nat.shiftLeft b1.toNat 1))
        (Nat.lor (Nat.shiftLeft b2.toNat 2) (Nat.shiftLeft b3.toNat 3)) =
      b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl

theorem patK_eq (dm mv x y : Nat) : patK dm mv x y =
    (Nat.beq (mulK dm mv x y) 0).toNat +
      2 * (Nat.beq (mulK dm mv (mulK dm mv x y) (mulK dm mv x y)) 0).toNat +
      4 * (Nat.beq (mulK dm mv (mulK dm mv (mulK dm mv x y) (mulK dm mv x y))
        (mulK dm mv (mulK dm mv x y) (mulK dm mv x y))) 0).toNat +
      8 * (Nat.beq (mulK dm mv x y) (mulK dm mv y x)).toNat := by
  unfold patK
  rw [strictN_eq', strictN_eq']
  exact bits4 _ _ _ _

theorem patK_enc {dm mv : Nat} (hdm : dmOK dm = true) (hmv : mvOK mv = true) (x y : SE) :
    patK dm mv x.enc y.enc = patCode x y := by
  rw [patK_eq]
  simp only [mulK_enc hdm hmv, nbeq0_enc, nbeq_enc]
  rfl

theorem isInvK_enc {dm mv : Nat} (hdm : dmOK dm = true) (hmv : mvOK mv = true) (s : SE) :
    isInvK dm mv s.enc = Fus.isInv (· * ·) s := by
  unfold isInvK Fus.isInv
  rw [mulK_enc hdm hmv, band', bnot', nbeq0_enc, nbeq0_enc]
  rfl

theorem tup4 (a b c d a' b' c' d' : Bool) :
    ((a, b, c, d) == (a', b', c', d')) = true ↔
      a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat =
        a'.toNat + 2 * b'.toNat + 4 * c'.toNat + 8 * d'.toNat := by
  revert a b c d a' b' c' d'
  decide

theorem pairOk_iff (A : Fus.Data) (q : Array SE) (i j : Nat) :
    A.pairOk (· * ·) q i j = true ↔
      patCode (q.getD i 1) (q.getD j 1) = patCode (A.gens.getD i 1) (A.gens.getD j 1) :=
  tup4 _ _ _ _ _ _ _ _

theorem pat_of_pairOk {dm mv : Nat} (hdm : dmOK dm = true) (hmv : mvOK mv = true) {A : Fus.Data}
    {q : Array SE} {i j : Nat} {x y : SE} (hx : q.getD i 1 = x) (hy : q.getD j 1 = y)
    (h : A.pairOk (· * ·) q i j = true) :
    patK dm mv x.enc y.enc = patCode (A.gens.getD i 1) (A.gens.getD j 1) := by
  rw [patK_enc hdm hmv, ← hx, ← hy]
  exact (pairOk_iff A q i j).mp h

theorem lor_shl {x y : Nat} (k : Nat) (hx : x < 2 ^ k) : (x ||| y <<< k) = x + 2 ^ k * y := by
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_comm]

theorem pack_val (v q1 q2 q3 : SE) :
    pack v q1 q2 q3 = v.enc + 512 * q1.enc + 262144 * q2.enc + 134217728 * q3.enc := by
  have h0 := SE.enc_lt v
  have h1 := SE.enc_lt q1
  have h2 := SE.enc_lt q2
  have e1 : (v.enc ||| q1.enc <<< 9) = v.enc + 2 ^ 9 * q1.enc := lor_shl 9 (by omega)
  have e2 : (v.enc + 2 ^ 9 * q1.enc ||| q2.enc <<< 18) = v.enc + 2 ^ 9 * q1.enc + 2 ^ 18 * q2.enc :=
    lor_shl 18 (by omega)
  have e3 : (v.enc + 2 ^ 9 * q1.enc + 2 ^ 18 * q2.enc ||| q3.enc <<< 27) =
      v.enc + 2 ^ 9 * q1.enc + 2 ^ 18 * q2.enc + 2 ^ 27 * q3.enc := lor_shl 27 (by omega)
  change ((v.enc ||| q1.enc <<< 9) ||| q2.enc <<< 18) ||| q3.enc <<< 27 = _
  rw [e1, e2, e3]
  norm_num

theorem packP (v q1 q2 : SE) :
    pack v q1 q2 1 = Nat.lor (Nat.lor v.enc (Nat.shiftLeft q1.enc 9)) (Nat.shiftLeft q2.enc 18) := by
  unfold pack
  rw [show Nat.shiftLeft (SE.enc 1) 27 = 0 from rfl]
  exact Nat.or_zero _

theorem rd_pack (q0 q1 q2 q3 : SE) {i : Nat} (hi : i = 0 ∨ i = 9 ∨ i = 18 ∨ i = 27) :
    (pack q0 q1 q2 q3 >>> i) &&& 511 = (#[q0, q1, q2, q3].getD (i / 9) 1).enc := by
  have h0 := SE.enc_lt q0
  have h1 := SE.enc_lt q1
  have h2 := SE.enc_lt q2
  have h3 := SE.enc_lt q3
  have hm : ∀ x : Nat, x &&& 511 = x % 512 := fun x => Nat.and_two_pow_sub_one_eq_mod x 9
  rw [hm, Nat.shiftRight_eq_div_pow, pack_val]
  rcases hi with rfl | rfl | rfl | rfl
  · change _ = q0.enc
    norm_num
    omega
  · change _ = q1.enc
    norm_num
    omega
  · change _ = q2.enc
    norm_num
    omega
  · change _ = q3.enc
    norm_num
    omega

theorem evalFrom_cons (dm mv Q acc i : Nat) (w : List Nat) :
    evalFrom dm mv Q acc (i :: w) = evalFrom dm mv Q (mulK dm mv acc ((Q >>> i) &&& 511)) w := by
  change CFSG.KC.Enum.strictN (mulK dm mv acc (Nat.land (Nat.shiftRight Q i) 511))
    (fun acc => evalFrom dm mv Q acc w) = _
  rw [strictN_eq']
  rfl

theorem evalW_nil (q : Array SE) : Fus.evalW (· * ·) q [] = 1 := rfl

theorem evalW_append (q : Array SE) (u w : List Nat) :
    Fus.evalW (· * ·) q (u ++ w) = Fus.evalW (· * ·) q u * Fus.evalW (· * ·) q w := by
  have h := Fus.evalW_foldl q w (Fus.evalW (· * ·) q u)
  change (u ++ w).foldl (fun a i => a * q.getD i 1) 1 = _
  rw [List.foldl_append]
  exact h

theorem evalW_congr {q q' : Array SE} :
    ∀ u : List Nat, (∀ i ∈ u, q.getD i 1 = q'.getD i 1) →
      Fus.evalW (· * ·) q u = Fus.evalW (· * ·) q' u
  | [], _ => rfl
  | i :: u, h => by
    rw [Fus.evalW_cons, Fus.evalW_cons, h i List.mem_cons_self,
      evalW_congr u fun j hj => h j (List.mem_cons_of_mem _ hj)]

@[expose] def Let9 (w : List Nat) : Prop := ∀ i ∈ w, i = 0 ∨ i = 9 ∨ i = 18 ∨ i = 27

theorem evalFrom_enc {dm mv : Nat} (hdm : dmOK dm = true) (hmv : mvOK mv = true)
    (q0 q1 q2 q3 : SE) : ∀ (w : List Nat) (s : SE), Let9 w →
      evalFrom dm mv (pack q0 q1 q2 q3) s.enc w =
        (s * Fus.evalW (· * ·) #[q0, q1, q2, q3] (w.map (· / 9))).enc
  | [], s, _ => by rw [List.map_nil, evalW_nil, mul_one]; rfl
  | i :: w, s, h => by
    rw [evalFrom_cons, rd_pack q0 q1 q2 q3 (h i List.mem_cons_self), mulK_enc hdm hmv,
      evalFrom_enc hdm hmv q0 q1 q2 q3 w _ fun j hj => h j (List.mem_cons_of_mem _ hj),
      List.map_cons, Fus.evalW_cons, mul_assoc]

theorem evalWK_enc {dm mv : Nat} (hdm : dmOK dm = true) (hmv : mvOK mv = true)
    (q0 q1 q2 q3 : SE) {w : List Nat} (hw : Let9 w) :
    evalWK dm mv (pack q0 q1 q2 q3) w = (Fus.evalW (· * ·) #[q0, q1, q2, q3] (w.map (· / 9))).enc := by
  have := evalFrom_enc hdm hmv q0 q1 q2 q3 w 1 hw
  rw [one_mul] at this
  exact this

theorem walkM_cons (f : Nat → Nat → Bool) (a b : Nat) (L : List (Nat × Nat)) (m : Nat) :
    walkM f ((a, b) :: L) m = Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (walkM f L (m / 2)) (f a b && walkM f L (m / 2))
        (Nat.beq (m % 2) 1)) true (Nat.beq m 0) := by
  change Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (CFSG.KC.Enum.strictB (Nat.shiftRight m 1) (walkM f L))
        (Bool.and' (f a b) (CFSG.KC.Enum.strictB (Nat.shiftRight m 1) (walkM f L)))
        (Nat.beq (Nat.land m 1) 1)) true (Nat.beq m 0) = _
  have e1 : Nat.land m 1 = m % 2 := Nat.and_one_is_mod m
  have e2 : Nat.shiftRight m 1 = m / 2 := by
    change m >>> 1 = m / 2
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
  rw [strictB_eq', band', e1, e2]

theorem walkM_spec (f : Nat → Nat → Bool) : ∀ (L : List (Nat × Nat)) (m : Nat), walkM f L m = true →
    ∀ n (h : n < L.length), m.testBit n = true → f L[n].1 L[n].2 = true
  | [], _, _, n, h, _ => absurd h (Nat.not_lt_zero n)
  | (a, b) :: L, m, hw, n, hn, hb => by
    rw [walkM_cons] at hw
    cases h0 : Nat.beq m 0
    · rw [h0] at hw
      have hw' : Bool.rec (motive := fun _ => Bool) (walkM f L (m / 2)) (f a b && walkM f L (m / 2))
          (Nat.beq (m % 2) 1) = true := hw
      have hr : walkM f L (m / 2) = true := by
        cases h1 : Nat.beq (m % 2) 1
        · rw [h1] at hw'
          exact hw'
        · rw [h1] at hw'
          exact (Bool.and_eq_true _ _).mp hw' |>.2
      cases n with
      | zero =>
        rw [Nat.testBit_zero, decide_eq_true_eq] at hb
        have h1 : Nat.beq (m % 2) 1 = true := by rw [Nat.beq_eq]; exact hb
        rw [h1] at hw'
        exact ((Bool.and_eq_true _ _).mp hw').1
      | succ n =>
        rw [Nat.testBit_add_one] at hb
        exact walkM_spec f L (m / 2) hr n (by simpa using hn) hb
    · rw [Nat.beq_eq] at h0
      subst h0
      rw [Nat.zero_testBit] at hb
      exact absurd hb (by decide)

@[expose] noncomputable def rowKF (dm mv x : Nat) (L : List (Nat × Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun e _ ih j => Nat.lor (Prod.rec (motive := fun _ => Nat) (fun c _ =>
      Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.add (Nat.shiftLeft (patK dm mv x c) (nat_lit 7))
        (nat_lit 64)) j)) e)
      (CFSG.KC.Enum.strictN (Nat.succ j) ih)) L

theorem rowKF_bit (dm mv x : Nat) : ∀ (L : List (Nat × Nat)) (j n : Nat) (h : n < L.length),
    (rowKF dm mv x L j).testBit (128 * patK dm mv x L[n].1 + 64 + j + n) = true
  | [], _, n, h => absurd h (Nat.not_lt_zero n)
  | (c, r) :: L, j, n, h => by
    change (Nat.lor (Nat.shiftLeft 1 (Nat.add (Nat.add (Nat.shiftLeft (patK dm mv x c) 7) 64) j))
      (CFSG.KC.Enum.strictN (Nat.succ j) (rowKF dm mv x L))).testBit _ = true
    rw [strictN_eq']
    change ((1 <<< ((patK dm mv x c <<< 7) + 64 + j)) ||| rowKF dm mv x L (j + 1)).testBit _ = true
    rw [Nat.testBit_or, Bool.or_eq_true]
    cases n with
    | zero =>
      left
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow, Nat.shiftLeft_eq]
      simp only [List.getElem_cons_zero, decide_eq_true_eq]
      ring
    | succ n =>
      right
      have hn : n < L.length := by simpa using h
      have := rowKF_bit dm mv x L (j + 1) n hn
      have e : ((c, r) :: L)[n + 1].1 = L[n].1 := rfl
      rw [e, show 128 * patK dm mv x L[n].1 + 64 + j + (n + 1) =
        128 * patK dm mv x L[n].1 + 64 + (j + 1) + n by ring]
      exact this

theorem rowK_bit (dm mv x : Nat) (L : List (Nat × Nat)) (n : Nat) (h : n < L.length) :
    (rowK dm mv x L).testBit (128 * patK dm mv x L[n].1 + 64 + n) = true :=
  rowKF_bit dm mv x L 0 n h

theorem m87_eq : m87 = 2 ^ 87 - 1 := by decide +kernel

theorem lane_bit {R P n : Nat} (hR : R.testBit (128 * P + 64 + n) = true) (hn : n < 87) :
    (lane R P).testBit n = true := by
  change ((R >>> ((P <<< 7) + 64)) &&& m87).testBit n = true
  rw [m87_eq, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight,
    Nat.shiftLeft_eq]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, hn⟩
  rw [show P * 2 ^ 7 + 64 + n = 128 * P + 64 + n by ring]
  exact hR

theorem rowsOK_spec (dm mv : Nat) (L : List (Nat × Nat)) : ∀ (R : List (Nat × Nat)),
    rowsOK dm mv R L = true → ∀ n (h : n < R.length),
      Nat.lor (rowK dm mv R[n].1 L) (Nat.land R[n].2 18446744073709551615) = R[n].2
  | [], _, n, h => absurd h (Nat.not_lt_zero n)
  | (c, r) :: R, hr, n, hn => by
    have h' : Bool.and' (Nat.beq (Nat.lor (rowK dm mv c L) (Nat.land r 18446744073709551615)) r)
        (rowsOK dm mv R L) = true := hr
    rw [band', Bool.and_eq_true] at h'
    cases n with
    | zero => exact Nat.eq_of_beq_eq_true h'.1
    | succ n => exact rowsOK_spec dm mv L R h'.2 n (by simpa using hn)

theorem row_bit {dm mv : Nat} {L : List (Nat × Nat)} (hrows : rowsOK dm mv L L = true) {k : Nat}
    (hk : k < L.length) {t : Nat} (ht : (rowK dm mv L[k].1 L).testBit t = true) :
    L[k].2.testBit t = true := by
  rw [← rowsOK_spec dm mv L L hrows k hk]
  change ((rowK dm mv L[k].1 L) ||| (L[k].2 &&& 18446744073709551615)).testBit t = true
  rw [Nat.testBit_or, ht, Bool.true_or]

theorem codeMask_spec : ∀ (L : List (Nat × Nat)) (c : Nat), (codeMask L).testBit c = true →
    ∃ n, ∃ h : n < L.length, L[n].1 = c
  | [], c, h => by
    change Nat.testBit 0 c = true at h
    rw [Nat.zero_testBit] at h
    exact absurd h (by decide)
  | (a, b) :: L, c, h => by
    change ((1 <<< a) ||| codeMask L).testBit c = true at h
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_eq] at h
    rcases h with h | h
    · exact ⟨0, by simp, h⟩
    · obtain ⟨n, hn, e⟩ := codeMask_spec L c h
      exact ⟨n + 1, by simpa using hn, e⟩

theorem testBit_of {x n : Nat} (h : (x >>> n) &&& 1 = 1) : x.testBit n = true := by
  unfold Nat.testBit
  rw [Nat.and_comm, h]
  rfl

theorem pos_of_inv {dm mv : Nat} (hdm : dmOK dm = true) (hmv : mvOK mv = true)
    {L : List (Nat × Nat)} (hinvs : invsOK dm mv L = true) {s : SE}
    (hs : Fus.isInv (· * ·) s = true) : ∃ n, ∃ h : n < L.length, L[n].1 = s.enc := by
  have hA : allBelow (nat_lit 512) (fun c => Bool.or' (Bool.not' (isInvK dm mv c))
      (Nat.beq (Nat.land (Nat.shiftRight (codeMask L) c) 1) 1)) = true := by
    have h' := hinvs
    unfold invsOK at h'
    rw [strictB_eq'] at h'
    generalize (nat_lit 512) = N at h' ⊢
    exact h'
  have h1 := allBelow_spec hA s.enc (SE.enc_lt s)
  rw [bor', bnot', isInvK_enc hdm hmv, hs, Bool.not_true, Bool.false_or, Nat.beq_eq] at h1
  exact codeMask_spec L s.enc (testBit_of h1)

theorem stage1_eq (dm mv CT BP v Rv P : Nat) (L : List (Nat × Nat)) (t1 t2 t3 : Test)
    (IK EW : List (Nat × List Nat)) (zw : List Nat) (uE uF : Bool) (good : Nat → Bool) (c1 R1 : Nat) :
    stage1 dm mv CT BP v Rv P L t1 t2 t3 IK EW zw uE uF good c1 R1 =
      walkM (stage2 dm mv CT BP (Nat.lor v (Nat.shiftLeft c1 9))
        (Nat.land (lane Rv (nib P 3)) (lane R1 (nib P 4))) (nib P 5) L t1 t2 t3 IK EW zw uE uF good) L
        (Nat.land (lane Rv (nib P 1)) (lane R1 (nib P 2))) := by
  unfold stage1
  rw [strictB_eq', strictB_eq']

theorem stage2_eq (dm mv CT BP : Nat) (v q1 : SE) (A3 p23 : Nat) (L : List (Nat × Nat))
    (t1 t2 t3 : Test) (IK EW : List (Nat × List Nat)) (zw : List Nat) (uE uF : Bool)
    (good : Nat → Bool) (q2 : SE) (R2 : Nat) :
    stage2 dm mv CT BP (Nat.lor v.enc (Nat.shiftLeft q1.enc 9)) A3 p23 L t1 t2 t3 IK EW zw uE uF good
        q2.enc R2 =
      ((!(pairOkK (evalWK dm mv (pack v q1 q2 1) (preK t1)) t1 &&
          (pairOkK (evalWK dm mv (pack v q1 q2 1) (preK t2)) t2 &&
            pairOkK (evalWK dm mv (pack v q1 q2 1) (preK t3)) t3))) ||
        walkM (stage3 dm mv CT BP (pack v q1 q2 1) (evalWK dm mv (pack v q1 q2 1) (preK t1))
          (evalWK dm mv (pack v q1 q2 1) (preK t2)) (evalWK dm mv (pack v q1 q2 1) (preK t3))
          t1 t2 t3 IK EW zw uE uF good) L (Nat.land A3 (lane R2 p23))) := by
  unfold stage2
  rw [strictB_eq', strictB_eq', strictB_eq', strictB_eq', strictB_eq', bor', bnot', band', band',
    packP]

theorem stage3_eq (dm mv CT BP : Nat) (v q1 q2 : SE) (x1 x2 x3 : Nat) (t1 t2 t3 : Test)
    (IK EW : List (Nat × List Nat)) (zw : List Nat) (uE uF : Bool) (good : Nat → Bool) (q3 : SE)
    (R3 : Nat) :
    stage3 dm mv CT BP (pack v q1 q2 1) x1 x2 x3 t1 t2 t3 IK EW zw uE uF good q3.enc R3 =
      ((!(triOkK dm mv (pack v q1 q2 q3) x1 t1 && (triOkK dm mv (pack v q1 q2 q3) x2 t2 &&
          triOkK dm mv (pack v q1 q2 q3) x3 t3))) ||
        outK dm mv CT BP (pack v q1 q2 q3) IK EW zw uE uF good) := by
  unfold stage3
  rw [strictB_eq', bor', bnot', band', band', packP]
  rfl

theorem range_getD (f : ℕ → SE) {k : ℕ} (hk : k < 32) :
    ((List.range 32).toArray.map f).getD k 1 = f k := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
    List.getElem?_range hk]
  rfl

theorem condB_facts {A : Fus.Data} (TF : Fus.Data.TableFacts A) {q : Array SE}
    (hc : A.condB (· * ·) q = true) :
    (∀ k < 32, ∀ i < 4, A.img (· * ·) q (A.mi k i) = A.img (· * ·) q k * q.getD i 1) ∧
      (∀ k < 32, A.img (· * ·) q k = 1 → k = 0) := by
  unfold Fus.Data.condB at hc
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, Bool.or_eq_true,
    bne_iff_ne] at hc
  refine ⟨fun k hk i hi => ?_, fun k hk h1 => ?_⟩
  · have := hc.1 k hk i hi
    rwa [range_getD _ (TF.mi_lt k hk i hi), range_getD _ hk] at this
  · rcases hc.2 k hk with h | h
    · exact h
    · rw [range_getD _ hk] at h
      exact absurd h1 h

theorem img_walk {A : Fus.Data} (TF : Fus.Data.TableFacts A) {q : Array SE}
    (hm : ∀ k < 32, ∀ i < 4, A.img (· * ·) q (A.mi k i) = A.img (· * ·) q k * q.getD i 1) :
    ∀ (u : List Nat), (∀ i ∈ u, i < 4) → ∀ k < 32,
      u.foldl (fun k i => A.mi k i) k < 32 ∧
        A.img (· * ·) q (u.foldl (fun k i => A.mi k i) k) =
          A.img (· * ·) q k * Fus.evalW (· * ·) q u
  | [], _, k, hk => ⟨hk, by rw [evalW_nil, mul_one]; rfl⟩
  | i :: u, hu, k, hk => by
    have hi := hu i List.mem_cons_self
    obtain ⟨h1, h2⟩ := img_walk TF hm u (fun j hj => hu j (List.mem_cons_of_mem _ hj)) (A.mi k i)
      (TF.mi_lt k hk i hi)
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, hm k hk i hi, Fus.evalW_cons, mul_assoc]

theorem img_zero {A : Fus.Data} (TF : Fus.Data.TableFacts A) (q : Array SE) :
    A.img (· * ·) q 0 = 1 := by
  have h0 := TF.words0
  have e : A.words.getD 0 [] = [] := by
    rw [Array.getD_eq_getD_getElem?] at h0 ⊢
    revert h0
    cases A.words[0]? with
    | none => exact fun h0 => absurd h0 (by simp)
    | some w => exact fun h0 => h0
  unfold Fus.Data.img
  rw [e]
  rfl

theorem let9_div {w : List Nat} (hw : Let9 w) : ∀ i ∈ w.map (· / 9), i < 4 := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  rcases hw j hj with rfl | rfl | rfl | rfl <;> decide

theorem okK_test {A : Fus.Data} (TF : Fus.Data.TableFacts A) {q : Array SE}
    (hc : A.condB (· * ·) q = true) {w : List Nat} (hw : Let9 w) {rel : Bool}
    (hr : (walkIdx A w == 0) = rel) :
    okK rel (Fus.evalW (· * ·) q (w.map (· / 9))).enc = true := by
  obtain ⟨hm, h1⟩ := condB_facts TF hc
  obtain ⟨hlt, he⟩ := img_walk TF hm (w.map (· / 9)) (let9_div hw) 0 (by decide)
  rw [img_zero TF, one_mul] at he
  have hwi : walkIdx A w = (w.map (· / 9)).foldl (fun k i => A.mi k i) 0 := by
    unfold walkIdx
    rw [List.foldl_map]
  rw [← he, ← hwi]
  rw [← hwi] at hlt
  cases rel
  · have hne : walkIdx A w ≠ 0 := by simpa using hr
    have hn1 : A.img (· * ·) q (walkIdx A w) ≠ 1 := fun h => hne (h1 _ hlt h)
    change Bool.not' (Nat.beq _ 0) = true
    rw [bnot', nbeq0_enc, Bool.not_eq_true', beq_eq_false_iff_ne]
    exact hn1
  · have he0 : walkIdx A w = 0 := by simpa using hr
    rw [he0, img_zero TF]
    rfl

theorem badBK_spec (dm mv CT BP Q : Nat) : ∀ IK : List (Nat × List Nat), badBK dm mv CT BP Q IK = true →
    ∃ r ∈ IK, (BP >>> (r.1 + clsK CT (evalWK dm mv Q r.2))) &&& 1 = 1
  | [], h => absurd h Bool.false_ne_true
  | (c, w) :: IK, h => by
    have h' : Bool.or' (Nat.beq (Nat.land (Nat.shiftRight BP (Nat.add c (clsK CT (evalWK dm mv Q w))))
        1) 1) (badBK dm mv CT BP Q IK) = true := h
    rw [bor', Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact ⟨(c, w), List.mem_cons_self, Nat.eq_of_beq_eq_true h'⟩
    · obtain ⟨r, hr, e⟩ := badBK_spec dm mv CT BP Q IK h'
      exact ⟨r, List.mem_cons_of_mem _ hr, e⟩

theorem diffK_spec (dm mv Q : Nat) (pred : Nat → Bool) : ∀ EW : List (Nat × List Nat),
    diffK dm mv Q pred EW = true → ∃ r ∈ EW, pred r.1 ≠ pred (evalWK dm mv Q r.2)
  | [], h => absurd h Bool.false_ne_true
  | (e, w) :: EW, h => by
    have h' : Bool.or' (Bool.rec (motive := fun _ => Bool) (pred (evalWK dm mv Q w))
        (Bool.not' (pred (evalWK dm mv Q w))) (pred e)) (diffK dm mv Q pred EW) = true := h
    rw [bor', Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · refine ⟨(e, w), List.mem_cons_self, ?_⟩
      change pred e ≠ pred (evalWK dm mv Q w)
      revert h'
      rw [bnot']
      cases pred e <;> cases pred (evalWK dm mv Q w) <;> decide
    · obtain ⟨r, hr, e⟩ := diffK_spec dm mv Q pred EW h'
      exact ⟨r, List.mem_cons_of_mem _ hr, e⟩

theorem fin512b : allBelow 512 (fun c => Nat.beq (c &&& 5) (4 * (c / 4 % 4 % 2) + c % 4 % 2) &&
    Nat.beq (nib 5440 (c >>> 6)) (4 * SE.parF1 (Fin.ofNat 8 (c / 64)) + SE.parF2 (Fin.ofNat 8 (c / 64)))
      || Nat.blt 255 c) = true := by
  decide +kernel

theorem parF_le (d : Fin 8) : SE.parF1 d ≤ 1 ∧ SE.parF2 d ≤ 1 := by
  revert d
  decide

theorem predEK_enc (s : SE) : predEK s.enc = decide (SE.predE s) := by
  obtain ⟨hd, h0, h1, h2⟩ := enc_parts s
  have hl := SE.enc_lt s
  have hb := allBelow_spec fin512b s.enc hl
  unfold predEK SE.predE
  rw [band']
  have e256 : Nat.blt s.enc 256 = decide (s.d.val < 4) := by
    rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_eq]
    omega
  rw [e256]
  by_cases hd4 : s.d.val < 4
  · have hb' : Nat.beq (s.enc &&& 5) (4 * (s.enc / 4 % 4 % 2) + s.enc % 4 % 2) = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at hb
      rcases hb with hb | hb
      · exact hb.1
      · omega
    have e5 := Nat.eq_of_beq_eq_true hb'
    have e1 : s.enc / 4 % 4 = s.v1.val := by unfold SE.enc; have := ZMod.val_lt s.v1; have := ZMod.val_lt s.v2; omega
    have e2 : s.enc % 4 = s.v2.val := by unfold SE.enc; have := ZMod.val_lt s.v2; omega
    rw [e1, e2] at e5
    change (decide (s.d.val < 4) && Nat.beq (s.enc &&& 5) 0) = _
    rw [e5]
    simp only [hd4, decide_true, Bool.true_and, true_and]
    rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_eq]
    omega
  · simp only [hd4, decide_false, Bool.false_and, false_and]

theorem predFK_enc (s : SE) : predFK s.enc = decide (SE.predF s) := by
  obtain ⟨hd, h0, h1, h2⟩ := enc_parts s
  have hl := SE.enc_lt s
  have hb := allBelow_spec fin512b s.enc hl
  unfold predFK SE.predF
  rw [band']
  have e256 : Nat.blt s.enc 256 = decide (s.d.val < 4) := by
    rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_eq]
    omega
  rw [e256]
  by_cases hd4 : s.d.val < 4
  · simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at hb
    have hb' : Nat.beq (s.enc &&& 5) (4 * (s.enc / 4 % 4 % 2) + s.enc % 4 % 2) = true ∧
        Nat.beq (nib 5440 (s.enc >>> 6)) (4 * SE.parF1 (Fin.ofNat 8 (s.enc / 64)) +
          SE.parF2 (Fin.ofNat 8 (s.enc / 64))) = true := by
      rcases hb with hb | hb
      · exact hb
      · omega
    have e5 := Nat.eq_of_beq_eq_true hb'.1
    have en := Nat.eq_of_beq_eq_true hb'.2
    have ed : Fin.ofNat 8 (s.enc / 64) = s.d := by
      ext
      rw [Fin.val_ofNat, hd, Nat.mod_eq_of_lt s.d.isLt]
    rw [ed] at en
    have e1 : s.enc / 4 % 4 = s.v1.val := by unfold SE.enc; have := ZMod.val_lt s.v1; have := ZMod.val_lt s.v2; omega
    have e2 : s.enc % 4 = s.v2.val := by unfold SE.enc; have := ZMod.val_lt s.v2; omega
    rw [e1, e2] at e5
    have hp := parF_le s.d
    change (decide (s.d.val < 4) && Nat.beq (s.enc &&& 5) (nib 5440 (s.enc >>> 6))) = _
    rw [e5, en]
    simp only [hd4, decide_true, Bool.true_and, true_and]
    rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_eq]
    omega
  · simp only [hd4, decide_false, Bool.false_and, false_and]

theorem clsArr_lt : (Array.toList SE.clsArr).all (fun x => Nat.blt x 9) = true := by decide +kernel

theorem clsTab_lt (s : SE) : SE.clsTab s < 9 := by
  have hs : s.enc < SE.clsArr.size := by
    have := SE.enc_lt s
    have e : SE.clsArr.size = 512 := by decide +kernel
    omega
  have h := List.all_eq_true.mp clsArr_lt (SE.clsArr.toList[s.enc]'(by simpa using hs))
    (List.getElem_mem _)
  rw [Nat.blt_eq] at h
  rw [SE.clsTab, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs, Option.getD_some]
  rwa [Array.getElem_toList] at h

theorem word9_let9 {A : Fus.Data} (TF : Fus.Data.TableFacts A) {k : Nat} (hk : k < 32) :
    Let9 (word9 A k) := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  have := TF.words_lt k hk j hj
  interval_cases j <;> simp

theorem word9_div (A : Fus.Data) (k : Nat) : (word9 A k).map (· / 9) = A.words.getD k [] := by
  unfold word9
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (A.words.getD k [])]
  apply List.map_congr_left
  intro j _
  simp

theorem let9_of_pre {pr : List Nat} (h : ∀ i ∈ pr, i = 0 ∨ i = 9 ∨ i = 18) : Let9 pr := by
  intro i hi
  rcases h i hi with h | h | h <;> simp [h]

theorem pre_val {dm mv : Nat} (hdm : dmOK dm = true) (hmv : mvOK mv = true) (v q1 q2 q3 : SE)
    {pr : List Nat} (h : ∀ i ∈ pr, i = 0 ∨ i = 9 ∨ i = 18) :
    evalWK dm mv (pack v q1 q2 1) pr =
      (Fus.evalW (· * ·) #[v, q1, q2, q3] (pr.map (· / 9))).enc := by
  rw [evalWK_enc hdm hmv _ _ _ _ (let9_of_pre h)]
  congr 1
  apply evalW_congr
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  rcases h j hj with rfl | rfl | rfl <;> rfl

theorem pairOkK_ok {dm mv : Nat} (hdm : dmOK dm = true) (hmv : mvOK mv = true) {A : Fus.Data}
    (TF : Fus.Data.TableFacts A) {v q1 q2 q3 : SE} (hc : A.condB (· * ·) #[v, q1, q2, q3] = true)
    {pr sf : List Nat} {r : Bool} (ht : TestRel A (pr, sf, r)) :
    pairOkK (evalWK dm mv (pack v q1 q2 1) (preK (pr, sf, r))) (pr, sf, r) = true := by
  obtain ⟨h1, -, h3⟩ := ht
  cases sf with
  | nil =>
    change okK r (evalWK dm mv (pack v q1 q2 1) pr) = true
    rw [pre_val hdm hmv v q1 q2 q3 h1]
    change (walkIdx A (pr ++ []) == 0) = r at h3
    rw [List.append_nil] at h3
    exact okK_test TF hc (let9_of_pre h1) h3
  | cons _ _ => rfl

theorem triOkK_ok {dm mv : Nat} (hdm : dmOK dm = true) (hmv : mvOK mv = true) {A : Fus.Data}
    (TF : Fus.Data.TableFacts A) {v q1 q2 q3 : SE} (hc : A.condB (· * ·) #[v, q1, q2, q3] = true)
    {pr sf : List Nat} {r : Bool} (ht : TestRel A (pr, sf, r)) :
    triOkK dm mv (pack v q1 q2 q3) (evalWK dm mv (pack v q1 q2 1) (preK (pr, sf, r))) (pr, sf, r) =
      true := by
  obtain ⟨h1, h2, h3⟩ := ht
  change okK r (evalFrom dm mv (pack v q1 q2 q3) (evalWK dm mv (pack v q1 q2 1) pr) sf) = true
  rw [pre_val hdm hmv v q1 q2 q3 h1, evalFrom_enc hdm hmv v q1 q2 q3 sf _ h2, ← evalW_append,
    ← List.map_append]
  have hl : Let9 (pr ++ sf) := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact let9_of_pre h1 i hi
    · exact h2 i hi
  exact okK_test TF hc hl h3

theorem fusRange_sound {dm mv CT : Nat} {L : List (Nat × Nat)} {A : Fus.Data} {D : FusT}
    {good : Nat → Bool} (hdm : dmOK dm = true) (hmv : mvOK mv = true)
    (hCT : ctOK CT (Array.toList SE.clsArr) = true) (hrows : rowsOK dm mv L L = true)
    (hinvs : invsOK dm mv L = true) (hlen : L.length ≤ 87) (ht : A.tableOk (· * ·) = true)
    (hD : FusRel A D)
    (hgood : ∀ q1 q2 q3 : SE, good (pack A.target q1 q2 q3) = true →
      A.good (· * ·) #[A.target, q1, q2, q3] = true)
    (hc : fusRange dm mv CT L D good 0 87 = true) : FusHyp A := by
  obtain ⟨v, P, ⟨⟨pr1, sf1, r1⟩, ⟨pr2, sf2, r2⟩, ⟨pr3, sf3, r3⟩⟩, IK, BP, EW, zw, uE, uF⟩ := D
  obtain ⟨hv, hP, ht1, ht2, ht3, hIK, hBP, hEW, hzw, huE, huF⟩ := hD
  dsimp only at hv hP ht1 ht2 ht3 hIK hBP hEW hzw huE huF
  subst hv hIK hEW hzw huE huF
  have TF := Fus.Data.tableFacts ht
  intro q1 q2 q3 i1 i2 i3 p01 p02 p12 p03 p13 p23 hcB
  have hP0 := hP 0 (by decide)
  have hP1 := hP 1 (by decide)
  have hP2 := hP 2 (by decide)
  have hP3 := hP 3 (by decide)
  have hP4 := hP 4 (by decide)
  have hP5 := hP 5 (by decide)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hP0 hP1 hP2 hP3 hP4 hP5
  have P0 : patK dm mv A.target.enc q1.enc = nib P 0 :=
    (pat_of_pairOk hdm hmv rfl rfl p01).trans hP0.symm
  have P1 : patK dm mv A.target.enc q2.enc = nib P 1 :=
    (pat_of_pairOk hdm hmv rfl rfl p02).trans hP1.symm
  have P2 : patK dm mv q1.enc q2.enc = nib P 2 :=
    (pat_of_pairOk hdm hmv rfl rfl p12).trans hP2.symm
  have P3 : patK dm mv A.target.enc q3.enc = nib P 3 :=
    (pat_of_pairOk hdm hmv rfl rfl p03).trans hP3.symm
  have P4 : patK dm mv q1.enc q3.enc = nib P 4 :=
    (pat_of_pairOk hdm hmv rfl rfl p13).trans hP4.symm
  have P5 : patK dm mv q2.enc q3.enc = nib P 5 :=
    (pat_of_pairOk hdm hmv rfl rfl p23).trans hP5.symm
  obtain ⟨n1, hn1, e1⟩ := pos_of_inv hdm hmv hinvs i1
  obtain ⟨n2, hn2, e2⟩ := pos_of_inv hdm hmv hinvs i2
  obtain ⟨n3, hn3, e3⟩ := pos_of_inv hdm hmv hinvs i3
  have rv : ∀ {n : Nat} (hn : n < L.length) {k : Nat} {s : SE}, L[n].1 = s.enc →
      patK dm mv A.target.enc s.enc = k → (lane (rowK dm mv A.target.enc L) k).testBit n = true := by
    intro n hn k s es hk
    refine lane_bit ?_ (by omega)
    have := rowK_bit dm mv A.target.enc L n hn
    rwa [es, hk] at this
  have rr : ∀ {m : Nat} (hm : m < L.length) {s : SE}, L[m].1 = s.enc → ∀ {n : Nat} (hn : n < L.length)
      {k : Nat} {s' : SE}, L[n].1 = s'.enc → patK dm mv s.enc s'.enc = k →
      (lane L[m].2 k).testBit n = true := by
    intro m hm s es n hn k s' es' hk
    refine lane_bit (row_bit hrows hm ?_) (by omega)
    have := rowK_bit dm mv L[m].1 L n hn
    rwa [show patK dm mv L[m].1 L[n].1 = k by rw [es, es', hk]] at this
  rw [fusRange_eq, walkRF_iff] at hc
  have s1 := hc n1 hn1 (rv hn1 e1 P0) (Nat.zero_le _) (by omega)
  rw [stage1_eq, e1] at s1
  have b2 : (Nat.land (lane (rowK dm mv A.target.enc L) (nib P 1)) (lane L[n1].2 (nib P 2))).testBit
      n2 = true := by
    change ((lane _ _) &&& (lane _ _)).testBit n2 = true
    rw [Nat.testBit_and, rv hn2 e2 P1, rr hn1 e1 hn2 e2 P2]
    rfl
  have s2 := walkM_spec _ L _ s1 n2 hn2 b2
  rw [e2, stage2_eq, pairOkK_ok hdm hmv TF hcB ht1, pairOkK_ok hdm hmv TF hcB ht2,
    pairOkK_ok hdm hmv TF hcB ht3] at s2
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at s2
  have b3 : (Nat.land (Nat.land (lane (rowK dm mv A.target.enc L) (nib P 3)) (lane L[n1].2 (nib P 4)))
      (lane L[n2].2 (nib P 5))).testBit n3 = true := by
    change (((lane _ _) &&& (lane _ _)) &&& (lane _ _)).testBit n3 = true
    rw [Nat.testBit_and, Nat.testBit_and, rv hn3 e3 P3, rr hn1 e1 hn3 e3 P4, rr hn2 e2 hn3 e3 P5]
    rfl
  have s3 := walkM_spec _ L _ s2 n3 hn3 b3
  rw [e3, stage3_eq, triOkK_ok hdm hmv TF hcB ht1, triOkK_ok hdm hmv TF hcB ht2,
    triOkK_ok hdm hmv TF hcB ht3] at s3
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at s3
  have hw : ∀ k < 32, evalWK dm mv (pack A.target q1 q2 q3) (word9 A k) =
      (A.img (· * ·) #[A.target, q1, q2, q3] k).enc := by
    intro k hk
    rw [evalWK_enc hdm hmv _ _ _ _ (word9_let9 TF hk), word9_div]
    rfl
  unfold outK at s3
  rw [bor', bor', band', bor', band', band'] at s3
  simp only [Bool.or_eq_true, Bool.and_eq_true] at s3
  unfold Fus.Data.outB
  simp only [Bool.or_eq_true]
  rcases s3 with hb | ⟨hz, hd⟩ | hg
  ·
    left; left; left
    obtain ⟨r, hr, e⟩ := badBK_spec _ _ _ _ _ _ hb
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hk1, hk2⟩ := List.mem_filter.mp hk
    have hk32 : k < 32 := List.mem_range.mp hk1
    dsimp only at e
    rw [hw k hk32, clsK_enc hCT] at e
    have hbp := hBP _ (clsTab_lt _) _ (clsTab_lt _) (testBit_of e)
    unfold Fus.Data.badB
    rw [List.any_eq_true]
    refine ⟨k, hk1, ?_⟩
    rw [hk2, Bool.true_and]
    exact List.contains_iff_mem.mpr hbp
  ·
    have hfz : A.fixZ (· * ·) #[A.target, q1, q2, q3] = true := by
      rw [hw _ TF.zIdx_lt, Nat.beq_eq] at hz
      unfold Fus.Data.fixZ
      rw [beq_iff_eq]
      exact enc_inj hz
    rcases hd with ⟨hu, hd⟩ | ⟨hu, hd⟩
    · left; left; right
      obtain ⟨r, hr, e⟩ := diffK_spec _ _ _ _ _ hd
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
      have hk32 : k < 32 := List.mem_range.mp hk
      dsimp only at e
      rw [hw k hk32, predEK_enc, predEK_enc] at e
      unfold Fus.Data.badEB
      rw [hu, hfz, Bool.true_and, Bool.true_and, List.any_eq_true]
      exact ⟨k, hk, bne_iff_ne.mpr e⟩
    · left; right
      obtain ⟨r, hr, e⟩ := diffK_spec _ _ _ _ _ hd
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
      have hk32 : k < 32 := List.mem_range.mp hk
      dsimp only at e
      rw [hw k hk32, predFK_enc, predFK_enc] at e
      unfold Fus.Data.badFB
      rw [hu, hfz, Bool.true_and, Bool.true_and, List.any_eq_true]
      exact ⟨k, hk, bne_iff_ne.mpr e⟩
  ·
    right
    exact hgood q1 q2 q3 hg

set_option maxRecDepth 100000 in
theorem clsOk_of {W : List (Nat × Nat)} (h1 : clsWOK W = true) (h2 : clsCover W = true) :
    SE.clsOk = true := by
  unfold SE.clsOk
  rw [List.all_eq_true]
  intro s _
  cases hs : SE.isInvB s
  · rfl
  have hc := List.all_eq_true.mp h2 s (SE.mem_allList s)
  rw [hs, Bool.not_true, Bool.false_or, List.any_eq_true] at hc
  obtain ⟨p, hp, he⟩ := hc
  have he' : p.1 = s.enc := beq_iff_eq.mp he
  have hw := List.all_eq_true.mp h1 p hp
  rw [he', SE.dec_enc, Bool.and_eq_true] at hw
  rw [Bool.not_true, Bool.false_or, Bool.and_eq_true]
  refine ⟨hw.1, List.any_eq_true.mpr ⟨SE.dec p.2, SE.mem_allList _, ?_⟩⟩
  exact hw.2

end CFSG.KC.GHFus
