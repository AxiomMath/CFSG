module

public import Certificates.Data.Kernel.F4M3B
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8L34Inputs

public section

namespace CFSG.KC.F4M3B

open CFSG.Quasithin.H13.L34

variable {α β : Type}

@[expose] def MatT.map (f : α → β) (A : MatT α) : MatT β :=
  ⟨f A.l00, f A.h00, f A.l01, f A.h01, f A.l02, f A.h02, f A.l10, f A.h10, f A.l11, f A.h11,
    f A.l12, f A.h12, f A.l20, f A.h20, f A.l21, f A.h21, f A.l22, f A.h22⟩

@[expose] def mulD (o : Ops α) (A B : MatT α) : MatT α :=
  ⟨dl o A.l00 A.h00 B.l00 B.h00 A.l01 A.h01 B.l10 B.h10 A.l02 A.h02 B.l20 B.h20,
    dh o A.l00 A.h00 B.l00 B.h00 A.l01 A.h01 B.l10 B.h10 A.l02 A.h02 B.l20 B.h20,
    dl o A.l00 A.h00 B.l01 B.h01 A.l01 A.h01 B.l11 B.h11 A.l02 A.h02 B.l21 B.h21,
    dh o A.l00 A.h00 B.l01 B.h01 A.l01 A.h01 B.l11 B.h11 A.l02 A.h02 B.l21 B.h21,
    dl o A.l00 A.h00 B.l02 B.h02 A.l01 A.h01 B.l12 B.h12 A.l02 A.h02 B.l22 B.h22,
    dh o A.l00 A.h00 B.l02 B.h02 A.l01 A.h01 B.l12 B.h12 A.l02 A.h02 B.l22 B.h22,
    dl o A.l10 A.h10 B.l00 B.h00 A.l11 A.h11 B.l10 B.h10 A.l12 A.h12 B.l20 B.h20,
    dh o A.l10 A.h10 B.l00 B.h00 A.l11 A.h11 B.l10 B.h10 A.l12 A.h12 B.l20 B.h20,
    dl o A.l10 A.h10 B.l01 B.h01 A.l11 A.h11 B.l11 B.h11 A.l12 A.h12 B.l21 B.h21,
    dh o A.l10 A.h10 B.l01 B.h01 A.l11 A.h11 B.l11 B.h11 A.l12 A.h12 B.l21 B.h21,
    dl o A.l10 A.h10 B.l02 B.h02 A.l11 A.h11 B.l12 B.h12 A.l12 A.h12 B.l22 B.h22,
    dh o A.l10 A.h10 B.l02 B.h02 A.l11 A.h11 B.l12 B.h12 A.l12 A.h12 B.l22 B.h22,
    dl o A.l20 A.h20 B.l00 B.h00 A.l21 A.h21 B.l10 B.h10 A.l22 A.h22 B.l20 B.h20,
    dh o A.l20 A.h20 B.l00 B.h00 A.l21 A.h21 B.l10 B.h10 A.l22 A.h22 B.l20 B.h20,
    dl o A.l20 A.h20 B.l01 B.h01 A.l21 A.h21 B.l11 B.h11 A.l22 A.h22 B.l21 B.h21,
    dh o A.l20 A.h20 B.l01 B.h01 A.l21 A.h21 B.l11 B.h11 A.l22 A.h22 B.l21 B.h21,
    dl o A.l20 A.h20 B.l02 B.h02 A.l21 A.h21 B.l12 B.h12 A.l22 A.h22 B.l22 B.h22,
    dh o A.l20 A.h20 B.l02 B.h02 A.l21 A.h21 B.l12 B.h12 A.l22 A.h22 B.l22 B.h22⟩

@[expose] def chkD (o : Ops α) (A : MatT α) : α :=
  let A2 := mulD o A A
  let A3 := mulD o A2 A
  let A5 := mulD o A3 A2
  let A15 := mulD o (mulD o A5 A5) A5
  bor o (bor o (bor o (bnot o (isOne o (detL o A) (detH o A))) (bnot o (scal o A15)))
    (scal o A5)) (scal o A3)

theorem mulK_eq (o : Ops α) (hbd : ∀ y k, o.bd y k = k y) (A B : MatT α) (k : MatT α → α) :
    mulK o A B k = k (mulD o A B) := by
  simp only [mulK, ent, hbd, mulD]

theorem chkK_eq (o : Ops α) (hbd : ∀ y k, o.bd y k = k y) (A : MatT α) :
    chkK o A = chkD o A := by
  simp only [chkK, mulK_eq o hbd, chkD]

section map

variable (o : Ops α) (o' : Ops β) (f : α → β) (ha : ∀ p q, f (o.a p q) = o'.a (f p) (f q))
  (hx : ∀ p q, f (o.x p q) = o'.x (f p) (f q)) (ht : f o.t = o'.t)
include ha hx

theorem mulD_map (A B : MatT α) : (mulD o A B).map f = mulD o' (A.map f) (B.map f) := by
  simp only [mulD, MatT.map, dl, dh, pl, ph, ha, hx]

theorem detL_map (A : MatT α) : f (detL o A) = detL o' (A.map f) := by
  simp only [detL, MatT.map, tl, pl, ph, ha, hx]

theorem detH_map (A : MatT α) : f (detH o A) = detH o' (A.map f) := by
  simp only [detH, MatT.map, th, pl, ph, ha, hx]

include ht

theorem bnot_map (p : α) : f (bnot o p) = bnot o' (f p) := by
  simp only [bnot, hx, ht]

theorem bor_map (p q : α) : f (bor o p q) = bor o' (f p) (f q) := by
  simp only [bor, ha, hx]

theorem isOne_map (l h : α) : f (isOne o l h) = isOne o' (f l) (f h) := by
  simp only [isOne, ha, bnot_map o o' f ha hx ht]

theorem scal_map (A : MatT α) : f (scal o A) = scal o' (A.map f) := by
  simp only [scal, isZero, isEq, MatT.map, ha, hx, bnot_map o o' f ha hx ht]

theorem chkD_map (A : MatT α) : f (chkD o A) = chkD o' (A.map f) := by
  simp only [chkD, bor_map o o' f ha hx ht, bnot_map o o' f ha hx ht, isOne_map o o' f ha hx ht,
    scal_map o o' f ha hx ht, detL_map o o' f ha hx, detH_map o o' f ha hx, mulD_map o o' f ha hx]

end map

@[expose] def boolOps : Ops Bool := ⟨and, xor, true, fun y k => k y⟩

@[expose] def lb (x : Fin 4) : Bool := x.val.testBit 0

@[expose] def hb (x : Fin 4) : Bool := x.val.testBit 1

@[expose] def ofM3 (A : M3) : MatT Bool :=
  ⟨lb A.a00, hb A.a00, lb A.a01, hb A.a01, lb A.a02, hb A.a02, lb A.a10, hb A.a10, lb A.a11,
    hb A.a11, lb A.a12, hb A.a12, lb A.a20, hb A.a20, lb A.a21, hb A.a21, lb A.a22, hb A.a22⟩

theorem pl_enc : ∀ x y : Fin 4, pl boolOps (lb x) (hb x) (lb y) (hb y) = lb (cmul x y) := by
  decide +kernel

theorem ph_enc : ∀ x y : Fin 4, ph boolOps (lb x) (hb x) (lb y) (hb y) = hb (cmul x y) := by
  decide +kernel

theorem xl_enc : ∀ x y : Fin 4, boolOps.x (lb x) (lb y) = lb (cadd x y) := by decide +kernel

theorem xh_enc : ∀ x y : Fin 4, boolOps.x (hb x) (hb y) = hb (cadd x y) := by decide +kernel

theorem isOne_enc : ∀ x : Fin 4, isOne boolOps (lb x) (hb x) = decide (x = 1) := by
  decide +kernel

theorem isZero_enc : ∀ x : Fin 4, isZero boolOps (lb x) (hb x) = decide (x = 0) := by
  decide +kernel

theorem isEq_enc : ∀ x y : Fin 4, isEq boolOps (lb x) (hb x) (lb y) (hb y) = decide (x = y) := by
  decide +kernel

theorem a_bool (p q : Bool) : boolOps.a p q = (p && q) := rfl

theorem bor_bool (p q : Bool) : bor boolOps p q = (p || q) := by
  cases p <;> cases q <;> rfl

theorem bnot_bool (p : Bool) : bnot boolOps p = !p := by
  cases p <;> rfl

theorem mulD_ofM3 (A B : M3) : mulD boolOps (ofM3 A) (ofM3 B) = ofM3 (M3.mul A B) := by
  simp only [mulD, dl, dh, ofM3, pl_enc, ph_enc, xl_enc, xh_enc]
  rfl

theorem detL_ofM3 (A : M3) : detL boolOps (ofM3 A) = lb (M3.det A) := by
  simp only [detL, tl, ofM3, pl_enc, ph_enc, xl_enc]
  rfl

theorem detH_ofM3 (A : M3) : detH boolOps (ofM3 A) = hb (M3.det A) := by
  simp only [detH, th, ofM3, pl_enc, ph_enc, xh_enc]
  rfl

theorem scal_ofM3 (A : M3) : scal boolOps (ofM3 A) = decide A.IsScalar := by
  simp only [scal, ofM3, isZero_enc, isEq_enc, a_bool]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, M3.IsScalar]

theorem chkD_ofM3 (A : M3) : chkD boolOps (ofM3 A) = M3.check A := by
  simp only [chkD, mulD_ofM3, detL_ofM3, detH_ofM3, isOne_enc, scal_ofM3, bor_bool, bnot_bool]
  rfl

theorem frcN_eq (y : Nat) (k : Nat → Nat) : frcN y k = k y := by
  cases y <;> rfl

theorem frc_eq (y : Nat) (k : Nat → Bool) : frc y k = k y := by
  cases y <;> rfl

theorem pln_succ (j m : Nat) : pln j (m + 1) =
    2 ^ 2 ^ m * (pln j m + if j = m then 2 ^ 2 ^ m - 1 else 0) + pln j m := by
  have e : pln j (m + 1) = frcN (pln j m) fun p => Nat.add p (Nat.shiftLeft
      (Nat.add p (Bool.rec (motive := fun _ => Nat) 0 (Nat.sub (Nat.pow 2 (Nat.pow 2 m)) 1)
        (Nat.beq j m))) (Nat.pow 2 m)) := rfl
  rw [e, frcN_eq]
  by_cases h : j = m
  · subst h
    simp only [Nat.beq_refl, if_true]
    change pln j j + (pln j j + (2 ^ 2 ^ j - 1)) <<< 2 ^ j = _
    rw [Nat.shiftLeft_eq]
    ring
  · have hb : Nat.beq j m = false := by
      rw [Bool.eq_false_iff]
      exact fun h' => h (Nat.eq_of_beq_eq_true h')
    simp only [hb, h, if_false]
    change pln j m + (pln j m + 0) <<< 2 ^ m = _
    rw [Nat.shiftLeft_eq]
    ring

theorem pln_bit (j : Nat) : ∀ m c, (pln j m).testBit c = (decide (c < 2 ^ m) && c.testBit j)
  | 0, c => by
    change Nat.testBit 0 c = _
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp
    · simp [show ¬ c < 1 by omega]
  | m + 1, c => by
    have ih := pln_bit j m
    have hp : pln j m < 2 ^ 2 ^ m := by
      refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
      rw [ih]
      simp [show ¬ i < 2 ^ m by omega]
    rw [pln_succ, Nat.testBit_two_pow_mul_add _ hp]
    by_cases hc : c < 2 ^ m
    · simp only [hc, if_true, ih, decide_true, Bool.true_and]
      have : c < 2 ^ (m + 1) := by rw [Nat.pow_succ]; omega
      simp [this]
    · simp only [hc, if_false]
      obtain ⟨d, rfl⟩ : ∃ d, c = 2 ^ m + d := ⟨c - 2 ^ m, by omega⟩
      have hd : 2 ^ m + d - 2 ^ m = d := by omega
      rw [hd]
      have hlt : (2 ^ m + d < 2 ^ (m + 1)) = (d < 2 ^ m) := by
        rw [Nat.pow_succ]; apply propext; omega
      simp only [hlt]
      rcases Nat.lt_trichotomy j m with hj | rfl | hj
      · simp only [show j ≠ m by omega, if_false, Nat.add_zero, ih,
          Nat.testBit_two_pow_add_gt hj]
      · have h0 : pln j j = 0 := Nat.eq_of_testBit_eq fun i => by
          rw [ih, Nat.zero_testBit]
          by_cases hi : i < 2 ^ j
          · simp [hi, Nat.testBit_lt_two_pow hi]
          · simp [hi]
        simp only [h0, if_true, Nat.zero_add, Nat.testBit_two_pow_sub_one,
          Nat.testBit_two_pow_add_eq]
        by_cases hd : d < 2 ^ j
        · simp [hd, Nat.testBit_lt_two_pow hd]
        · simp [hd]
      · simp only [show j ≠ m by omega, if_false, Nat.add_zero, ih]
        by_cases hd : d < 2 ^ m
        · have hmj : 2 ^ (m + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
          rw [Nat.pow_succ] at hmj
          have h1 : Nat.testBit d j = false := Nat.testBit_lt_two_pow (by omega)
          have h2 : Nat.testBit (2 ^ m + d) j = false := Nat.testBit_lt_two_pow (by omega)
          rw [h1, h2]
        · simp [hd]

@[expose] def codeM (A : M3) : Nat :=
  A.a00.val + 4 * A.a01.val + 16 * A.a02.val + 64 * A.a10.val + 256 * A.a11.val +
    1024 * A.a12.val + 4096 * A.a20.val + 16384 * A.a21.val + 65536 * A.a22.val

macro "code_tac" : tactic => `(tactic| (
  rintro ⟨⟨a0, h0⟩, ⟨a1, h1⟩, ⟨a2, h2⟩, ⟨a3, h3⟩, ⟨a4, h4⟩, ⟨a5, h5⟩, ⟨a6, h6⟩, ⟨a7, h7⟩,
    ⟨a8, h8⟩⟩
  simp only [lb, hb, codeM, Nat.testBit_eq_decide_div_mod_eq, Nat.reducePow, decide_eq_decide]
  omega))

theorem c0 : ∀ A : M3, (codeM A).testBit 0 = lb A.a00 := by code_tac
theorem c1 : ∀ A : M3, (codeM A).testBit 1 = hb A.a00 := by code_tac
theorem c2 : ∀ A : M3, (codeM A).testBit 2 = lb A.a01 := by code_tac
theorem c3 : ∀ A : M3, (codeM A).testBit 3 = hb A.a01 := by code_tac
theorem c4 : ∀ A : M3, (codeM A).testBit 4 = lb A.a02 := by code_tac
theorem c5 : ∀ A : M3, (codeM A).testBit 5 = hb A.a02 := by code_tac
theorem c6 : ∀ A : M3, (codeM A).testBit 6 = lb A.a10 := by code_tac
theorem c7 : ∀ A : M3, (codeM A).testBit 7 = hb A.a10 := by code_tac
theorem c8 : ∀ A : M3, (codeM A).testBit 8 = lb A.a11 := by code_tac
theorem c9 : ∀ A : M3, (codeM A).testBit 9 = hb A.a11 := by code_tac
theorem c10 : ∀ A : M3, (codeM A).testBit 10 = lb A.a12 := by code_tac
theorem c11 : ∀ A : M3, (codeM A).testBit 11 = hb A.a12 := by code_tac
theorem c12 : ∀ A : M3, (codeM A).testBit 12 = lb A.a20 := by code_tac
theorem c13 : ∀ A : M3, (codeM A).testBit 13 = hb A.a20 := by code_tac
theorem c14 : ∀ A : M3, (codeM A).testBit 14 = lb A.a21 := by code_tac
theorem c15 : ∀ A : M3, (codeM A).testBit 15 = hb A.a21 := by code_tac
theorem c16 : ∀ A : M3, (codeM A).testBit 16 = lb A.a22 := by code_tac
theorem c17 : ∀ A : M3, (codeM A).testBit 17 = hb A.a22 := by code_tac

theorem codeM_lt : ∀ A : M3, codeM A < 2 ^ 18 := by
  rintro ⟨⟨a0, h0⟩, ⟨a1, h1⟩, ⟨a2, h2⟩, ⟨a3, h3⟩, ⟨a4, h4⟩, ⟨a5, h5⟩, ⟨a6, h6⟩, ⟨a7, h7⟩,
    ⟨a8, h8⟩⟩
  simp only [codeM, Nat.reducePow]
  omega

@[expose] noncomputable def plns (m : Nat) : MatT Nat :=
  ⟨pln 0 m, pln 1 m, pln 2 m, pln 3 m, pln 4 m, pln 5 m, pln 6 m, pln 7 m, pln 8 m, pln 9 m,
    pln 10 m, pln 11 m, pln 12 m, pln 13 m, pln 14 m, pln 15 m, pln 16 m, pln 17 m⟩

theorem chkN_eq {m : Nat} (h : chkN m = true) :
    chkK (natOps (2 ^ 2 ^ m - 1)) (plns m) = 2 ^ 2 ^ m - 1 := by
  simpa only [chkN, plnK, plns, frc_eq, Nat.beq_eq, Nat.pow_eq, Nat.sub_eq] using h

theorem check_of_chkN_le {m : Nat} (h : chkN m = true) (A : M3) (hc : codeM A < 2 ^ m) :
    M3.check A = true := by
  have hbit := congrArg (fun n => n.testBit (codeM A)) (chkN_eq h)
  rw [chkK_eq _ (fun y k => frcN_eq y k),
    chkD_map (natOps _) boolOps (fun n => n.testBit (codeM A))
      (fun p q => Nat.testBit_and p q (codeM A)) (fun p q => Nat.testBit_xor p q (codeM A))
      (by simp [natOps, boolOps, hc])] at hbit
  have hm : (plns m).map (fun n => n.testBit (codeM A)) = ofM3 A := by
    simp only [plns, MatT.map, pln_bit, hc, decide_true, Bool.true_and, c0, c1, c2, c3, c4, c5,
      c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, ofM3]
  rw [hm, chkD_ofM3, Nat.testBit_two_pow_sub_one] at hbit
  simpa [hc] using hbit

theorem check_of_chkN (h : chkN 18 = true) (A : M3) : M3.check A = true :=
  check_of_chkN_le h A (codeM_lt A)

end CFSG.KC.F4M3B

end
