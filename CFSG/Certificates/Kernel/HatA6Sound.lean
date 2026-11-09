module

public import Certificates.Data.Kernel.HatA6K
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Data.Fintype.Fin

public section

namespace CFSG.KC.HatA6

open CFSG.Quasithin.H13.HatE CFSG.Quasithin.H13.HatC CFSG.Quasithin.H13.HatM

theorem bAnd_iff' {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem testBit_fldR (M k j : Nat) :
    (fldR M k).testBit j = (decide (j < 6) && M.testBit (6 * k + j)) := by
  unfold fldR
  change ((M >>> (6 * k)) &&& 63).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight]
  have h63 : (63 : Nat).testBit j = decide (j < 6) := by
    have : (63 : Nat) = 2 ^ 6 - 1 := rfl
    rw [this, Nat.testBit_two_pow_sub_one]
  rw [h63, Bool.and_comm]

theorem fldR_lt (M k : Nat) : fldR M k < 64 := by
  unfold fldR
  change (M >>> (6 * k)) &&& 63 < 64
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem testBit_lt_64 {a j : Nat} (ha : a < 64) (hj : 6 ≤ j) : a.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (by
    calc (64 : Nat) = 2 ^ 6 := rfl
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj))

theorem testBit_pk6 (a b c d e f j : Nat) (ha : a < 64) (hb : b < 64) (hc : c < 64)
    (hd : d < 64) (he : e < 64) (_hf : f < 64) :
    (pk6 a b c d e f).testBit j =
      if j < 6 then a.testBit j else if j < 12 then b.testBit (j - 6)
      else if j < 18 then c.testBit (j - 12) else if j < 24 then d.testBit (j - 18)
      else if j < 30 then e.testBit (j - 24) else f.testBit (j - 30) := by
  unfold pk6
  change (a ||| (b <<< 6 ||| (c <<< 12 ||| (d <<< 18 ||| (e <<< 24 ||| f <<< 30))))).testBit j = _
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h1 : j < 6
  · simp [h1, show ¬ 6 ≤ j by omega, show ¬ 12 ≤ j by omega, show ¬ 18 ≤ j by omega,
      show ¬ 24 ≤ j by omega, show ¬ 30 ≤ j by omega]
  by_cases h2 : j < 12
  · simp [h1, h2, testBit_lt_64 ha (by omega : 6 ≤ j), show 6 ≤ j by omega,
      show ¬ 12 ≤ j by omega, show ¬ 18 ≤ j by omega, show ¬ 24 ≤ j by omega,
      show ¬ 30 ≤ j by omega]
  by_cases h3 : j < 18
  · simp [h1, h2, h3, testBit_lt_64 ha (by omega : 6 ≤ j), testBit_lt_64 hb (by omega : 6 ≤ j - 6),
      show 6 ≤ j by omega, show 12 ≤ j by omega, show ¬ 18 ≤ j by omega,
      show ¬ 24 ≤ j by omega, show ¬ 30 ≤ j by omega]
  by_cases h4 : j < 24
  · simp [h1, h2, h3, h4, testBit_lt_64 ha (by omega : 6 ≤ j),
      testBit_lt_64 hb (by omega : 6 ≤ j - 6), testBit_lt_64 hc (by omega : 6 ≤ j - 12),
      show 6 ≤ j by omega, show 12 ≤ j by omega, show 18 ≤ j by omega,
      show ¬ 24 ≤ j by omega, show ¬ 30 ≤ j by omega]
  by_cases h5 : j < 30
  · simp [h1, h2, h3, h4, h5, testBit_lt_64 ha (by omega : 6 ≤ j),
      testBit_lt_64 hb (by omega : 6 ≤ j - 6), testBit_lt_64 hc (by omega : 6 ≤ j - 12),
      testBit_lt_64 hd (by omega : 6 ≤ j - 18),
      show 6 ≤ j by omega, show 12 ≤ j by omega, show 18 ≤ j by omega,
      show 24 ≤ j by omega, show ¬ 30 ≤ j by omega]
  · simp [h1, h2, h3, h4, h5, testBit_lt_64 ha (by omega : 6 ≤ j),
      testBit_lt_64 hb (by omega : 6 ≤ j - 6), testBit_lt_64 hc (by omega : 6 ≤ j - 12),
      testBit_lt_64 hd (by omega : 6 ≤ j - 18), testBit_lt_64 he (by omega : 6 ≤ j - 24),
      show 6 ≤ j by omega, show 12 ≤ j by omega, show 18 ≤ j by omega,
      show 24 ≤ j by omega, show 30 ≤ j by omega]

theorem fldR_pk6 {a b c d e f : Nat} (ha : a < 64) (hb : b < 64) (hc : c < 64) (hd : d < 64)
    (he : e < 64) (hf : f < 64) :
    fldR (pk6 a b c d e f) 0 = a ∧ fldR (pk6 a b c d e f) 1 = b ∧ fldR (pk6 a b c d e f) 2 = c ∧
      fldR (pk6 a b c d e f) 3 = d ∧ fldR (pk6 a b c d e f) 4 = e ∧
      fldR (pk6 a b c d e f) 5 = f := by
  have key : ∀ k < 6, ∀ x : Nat, x < 64 →
      (∀ j < 6, (pk6 a b c d e f).testBit (6 * k + j) = x.testBit j) →
      fldR (pk6 a b c d e f) k = x := by
    intro k _ x hx h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [testBit_fldR]
    by_cases hj : j < 6
    · rw [decide_eq_true hj, Bool.true_and, h j hj]
    · rw [decide_eq_false hj, Bool.false_and, testBit_lt_64 hx (by omega)]
  refine ⟨key 0 (by omega) a ha fun j hj => ?_, key 1 (by omega) b hb fun j hj => ?_,
    key 2 (by omega) c hc fun j hj => ?_, key 3 (by omega) d hd fun j hj => ?_,
    key 4 (by omega) e he fun j hj => ?_, key 5 (by omega) f hf fun j hj => ?_⟩ <;>
    rw [testBit_pk6 _ _ _ _ _ _ _ ha hb hc hd he hf]
  · simp [hj]
  · simp [show ¬ 6 * 1 + j < 6 by omega, show 6 * 1 + j < 12 by omega]
  · simp [show ¬ 6 * 2 + j < 6 by omega, show ¬ 6 * 2 + j < 12 by omega,
      show 6 * 2 + j < 18 by omega]
  · simp [show ¬ 6 * 3 + j < 6 by omega, show ¬ 6 * 3 + j < 12 by omega,
      show ¬ 6 * 3 + j < 18 by omega, show 6 * 3 + j < 24 by omega]
  · simp [show ¬ 6 * 4 + j < 6 by omega, show ¬ 6 * 4 + j < 12 by omega,
      show ¬ 6 * 4 + j < 18 by omega, show ¬ 6 * 4 + j < 24 by omega,
      show 6 * 4 + j < 30 by omega]
  · simp [show ¬ 6 * 5 + j < 6 by omega, show ¬ 6 * 5 + j < 12 by omega,
      show ¬ 6 * 5 + j < 18 by omega, show ¬ 6 * 5 + j < 24 by omega,
      show ¬ 6 * 5 + j < 30 by omega]

theorem unpackL_pk6 {a b c d e f : Nat} (ha : a < 64) (hb : b < 64) (hc : c < 64) (hd : d < 64)
    (he : e < 64) (hf : f < 64) : unpackL (pk6 a b c d e f) = [a, b, c, d, e, f] := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := fldR_pk6 ha hb hc hd he hf
  rw [unpackL, h0, h1, h2, h3, h4, h5]

theorem pk6_lt {a b c d e f : Nat} (ha : a < 64) (hb : b < 64) (hc : c < 64) (hd : d < 64)
    (he : e < 64) (hf : f < 64) : pk6 a b c d e f < 2 ^ 36 := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_pk6 _ _ _ _ _ _ _ ha hb hc hd he hf]
  simp only [show ¬ j < 6 by omega, show ¬ j < 12 by omega, show ¬ j < 18 by omega,
    show ¬ j < 24 by omega, show ¬ j < 30 by omega, ite_false]
  exact testBit_lt_64 hf (by omega)

theorem pk6_fldR {X : Nat} (hX : X < 2 ^ 36) :
    pk6 (fldR X 0) (fldR X 1) (fldR X 2) (fldR X 3) (fldR X 4) (fldR X 5) = X := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_pk6 _ _ _ _ _ _ _ (fldR_lt _ _) (fldR_lt _ _) (fldR_lt _ _) (fldR_lt _ _)
    (fldR_lt _ _) (fldR_lt _ _)]
  simp only [testBit_fldR]
  by_cases h1 : j < 6
  · simp [h1]
  by_cases h2 : j < 12
  · simp [h1, h2, show j - 6 < 6 by omega, show 6 * 1 + (j - 6) = j by omega]
  by_cases h3 : j < 18
  · simp [h1, h2, h3, show j - 12 < 6 by omega, show 6 * 2 + (j - 12) = j by omega]
  by_cases h4 : j < 24
  · simp [h1, h2, h3, h4, show j - 18 < 6 by omega, show 6 * 3 + (j - 18) = j by omega]
  by_cases h5 : j < 30
  · simp [h1, h2, h3, h4, h5, show j - 24 < 6 by omega, show 6 * 4 + (j - 24) = j by omega]
  by_cases h6 : j < 36
  · simp [h1, h2, h3, h4, h5, show j - 30 < 6 by omega, show 6 * 5 + (j - 30) = j by omega]
  · simp only [h1, h2, h3, h4, h5, ite_false, show ¬ j - 30 < 6 by omega, decide_false,
      Bool.false_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX
      (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

theorem beq_unpackL {X Y : Nat} (hX : X < 2 ^ 36) (hY : Y < 2 ^ 36) :
    (unpackL X == unpackL Y) = Nat.beq X Y := by
  have inj : unpackL X = unpackL Y → X = Y := fun e => by
    simp only [unpackL, List.cons.injEq, and_true] at e
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := e
    rw [← pk6_fldR hX, ← pk6_fldR hY, e0, e1, e2, e3, e4, e5]
  by_cases hxy : X = Y
  · subst hxy
    rw [beq_self_eq_true, Nat.beq_refl]
  · have h1 : (unpackL X == unpackL Y) = false :=
      beq_eq_false_iff_ne.2 fun e => hxy (inj e)
    have h2 : Nat.beq X Y = false := by
      cases h : Nat.beq X Y
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hxy
    rw [h1, h2]

theorem hatBeq_bit (c n : Nat) : Nat.beq (Nat.land (Nat.shiftRight c n) 1) 1 = c.testBit n := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change Nat.beq ((c >>> n) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  cases h : decide (c / 2 ^ n % 2 = 1)
  · have h' : c / 2 ^ n % 2 ≠ 1 := by simpa using h
    cases h2 : Nat.beq (c / 2 ^ n % 2) 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h2) h'
  · have h' : c / 2 ^ n % 2 = 1 := by simpa using h
    rw [h']
    rfl

theorem sel_eq (M c n : Nat) (hn : n < 6) :
    (if c.testBit n = true then (unpackL M).getD n 0 else 0) =
      nIf(Nat.beq (Nat.land (Nat.shiftRight c n) 1) 1, fldR M n, 0) := by
  have hb := hatBeq_bit c n
  have hg : (unpackL M).getD n 0 = fldR M n := by
    interval_cases n <;> rfl
  rw [hb, hg]
  cases c.testBit n <;> rfl

theorem mactN_eq (M c : Nat) : ∀ n ≤ 6, mactN (unpackL M) c n =
    Nat.rec (motive := fun _ => Nat) 0 (fun n ih => Nat.xor ih
      (nIf(Nat.beq (Nat.land (Nat.shiftRight c n) 1) 1, fldR M n, 0))) n
  | 0, _ => rfl
  | n + 1, h => by
    rw [mactN, mactN_eq M c n (by omega), sel_eq M c n (by omega)]
    rfl

theorem mact_unpackL (M c : Nat) : mact (unpackL M) c = mactR M c :=
  mactN_eq M c 6 le_rfl

theorem mactR_lt (M c : Nat) : mactR M c < 64 := by
  have : ∀ n, Nat.rec (motive := fun _ => Nat) 0 (fun n ih => Nat.xor ih
      (nIf(Nat.beq (Nat.land (Nat.shiftRight c n) 1) 1, fldR M n, 0))) n < 2 ^ 6 := by
    intro n
    induction n with
    | zero => exact Nat.two_pow_pos 6
    | succ n ih =>
      refine Nat.xor_lt_two_pow ih ?_
      cases Nat.beq (Nat.land (Nat.shiftRight c n) 1) 1
      · exact Nat.two_pow_pos 6
      · exact fldR_lt M n
  exact this 6

theorem mmulR_lt (A B : Nat) : mmulR A B < 2 ^ 36 :=
  pk6_lt (mactR_lt _ _) (mactR_lt _ _) (mactR_lt _ _) (mactR_lt _ _) (mactR_lt _ _) (mactR_lt _ _)

theorem mmul_unpackL (A B : Nat) : mmul (unpackL A) (unpackL B) = unpackL (mmulR A B) := by
  have hf : mact (unpackL A) = mactR A := funext (mact_unpackL A)
  rw [mmulR, unpackL_pk6 (mactR_lt _ _) (mactR_lt _ _) (mactR_lt _ _) (mactR_lt _ _)
    (mactR_lt _ _) (mactR_lt _ _), mmul, hf]
  rfl

theorem idc_eq : idc = unpackL IDC := by
  rw [IDC, unpackL_pk6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  rfl

theorem omc_eq : omc = unpackL OMC := by
  rw [OMC, unpackL_pk6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  rfl

theorem a0c_eq : a0c = unpackL A0C := by
  rw [A0C, unpackL_pk6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  rfl

theorem IDC_lt : IDC < 2 ^ 36 :=
  pk6_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem OMC_lt : OMC < 2 ^ 36 :=
  pk6_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem powR_succ (M n : Nat) : powR M (n + 1) = mmulR M (powR M n) := rfl

theorem powR_lt (M : Nat) : ∀ n, powR M n < 2 ^ 36
  | 0 => IDC_lt
  | n + 1 => by rw [powR_succ]; exact mmulR_lt _ _

theorem powC_unpackL (M : Nat) : ∀ n, powC (unpackL M) n = unpackL (powR M n)
  | 0 => idc_eq
  | n + 1 => by rw [powC, powC_unpackL M n, mmul_unpackL, powR_succ]

theorem allR_eq (n : Nat) (f : Nat → Bool) : allR n f = (List.range n).all f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change bAnd(f n, allR n f) = _
    rw [ih, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_comm]
    cases f n <;> rfl

theorem injC_unpackL (M : Nat) : injC (unpackL M) = injR M := by
  rw [injR, allR_eq, injC]
  congr 1
  funext c
  rw [mact_unpackL]
  cases h : Nat.beq (mactR M (Nat.succ c)) 0
  · have : mactR M (c + 1) ≠ 0 := fun e => by
      rw [Nat.succ_eq_add_one, e] at h
      have h0 := Nat.beq_refl 0
      rw [h] at h0
      exact Bool.false_ne_true h0
    simp [this]
  · have : mactR M (c + 1) = 0 := Nat.eq_of_beq_eq_true h
    simp [this]

theorem inZ_unpackL {X : Nat} (hX : X < 2 ^ 36) : inZ (unpackL X) = inZR X := by
  rw [inZ, idc_eq, omc_eq, mmul_unpackL, beq_unpackL hX IDC_lt, beq_unpackL hX OMC_lt,
    beq_unpackL hX (mmulR_lt _ _), inZR]
  cases Nat.beq X IDC <;> cases Nat.beq X OMC <;> rfl

theorem fldR_mmulR0 (A B : Nat) : fldR (mmulR A B) 0 = mactR A (fldR B 0) :=
  (fldR_pk6 (mactR_lt _ _) (mactR_lt _ _) (mactR_lt _ _) (mactR_lt _ _) (mactR_lt _ _)
    (mactR_lt _ _)).1

theorem fldR_IDC0 : fldR IDC 0 = 1 := by
  rw [IDC]
  exact (fldR_pk6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).1

theorem mactR_one (M : Nat) : mactR M 1 = fldR M 0 := by
  have h : mactR M 1 = Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor 0 (fldR M 0)) 0) 0) 0)
    0) 0 := rfl
  rw [h]
  change 0 ^^^ fldR M 0 ^^^ 0 ^^^ 0 ^^^ 0 ^^^ 0 ^^^ 0 = _
  simp only [Nat.xor_zero, Nat.zero_xor]

theorem mactR_hsel (M x : Nat) : mactR M x = Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor
    (Nat.xor 0 (hselR x 0 (fldR M 0))) (hselR x 1 (fldR M 1))) (hselR x 2 (fldR M 2)))
    (hselR x 3 (fldR M 3))) (hselR x 4 (fldR M 4))) (hselR x 5 (fldR M 5)) := rfl

theorem hselR_xor (a b n v : Nat) :
    hselR (Nat.xor a b) n v = Nat.xor (hselR a n v) (hselR b n v) := by
  unfold hselR
  have hx : (Nat.xor a b).testBit n = (a.testBit n ^^ b.testBit n) := Nat.testBit_xor a b n
  rw [hatBeq_bit, hatBeq_bit, hatBeq_bit, hx]
  cases a.testBit n <;> cases b.testBit n
  · exact (Nat.xor_zero 0).symm
  · exact (Nat.zero_xor v).symm
  · exact (Nat.xor_zero v).symm
  · exact (Nat.xor_self v).symm

theorem hatXor4 (p q r s : Nat) :
    Nat.xor (Nat.xor p q) (Nat.xor r s) = Nat.xor (Nat.xor p r) (Nat.xor q s) := by
  change (p ^^^ q) ^^^ (r ^^^ s) = (p ^^^ r) ^^^ (q ^^^ s)
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases p.testBit i <;> cases q.testBit i <;> cases r.testBit i <;> cases s.testBit i <;> rfl

theorem mactR_xor (M a b : Nat) : mactR M (Nat.xor a b) = Nat.xor (mactR M a) (mactR M b) := by
  have key : ∀ k, Nat.rec (motive := fun _ => Nat) 0
      (fun n ih => Nat.xor ih (hselR (Nat.xor a b) n (fldR M n))) k =
      Nat.xor (Nat.rec (motive := fun _ => Nat) 0 (fun n ih => Nat.xor ih (hselR a n (fldR M n))) k)
        (Nat.rec (motive := fun _ => Nat) 0 (fun n ih => Nat.xor ih (hselR b n (fldR M n))) k) := by
    intro k
    induction k with
    | zero => exact (Nat.xor_zero 0).symm
    | succ k ih =>
      dsimp only
      rw [ih, hselR_xor]
      exact hatXor4 _ _ _ _
  exact key 6

theorem hselR_zero (n v : Nat) : hselR 0 n v = 0 := by
  unfold hselR
  rw [hatBeq_bit, Nat.zero_testBit]

theorem mactR_zero (M : Nat) : mactR M 0 = 0 := by
  rw [mactR_hsel]
  simp only [hselR_zero]
  rfl

theorem mactR_hselR (A x n v : Nat) : mactR A (hselR x n v) = hselR x n (mactR A v) := by
  unfold hselR
  cases Nat.beq (Nat.land (Nat.shiftRight x n) 1) 1
  · exact mactR_zero A
  · rfl

theorem mactR_mmulR (A B x : Nat) : mactR (mmulR A B) x = mactR A (mactR B x) := by
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := fldR_pk6 (mactR_lt A (fldR B 0)) (mactR_lt A (fldR B 1))
    (mactR_lt A (fldR B 2)) (mactR_lt A (fldR B 3)) (mactR_lt A (fldR B 4)) (mactR_lt A (fldR B 5))
  rw [mactR_hsel (mmulR A B) x, mactR_hsel B x, mmulR, f0, f1, f2, f3, f4, f5, mactR_xor,
    mactR_xor, mactR_xor, mactR_xor, mactR_xor, mactR_xor, mactR_zero, mactR_hselR, mactR_hselR,
    mactR_hselR, mactR_hselR, mactR_hselR, mactR_hselR]

theorem mactR_IDC : ∀ x < 64, mactR IDC x = x := by decide +kernel

theorem injR_of {M : Nat} (h : ∀ y, 0 < y → y < 64 → mactR M y ≠ 0) : injR M = true := by
  rw [injR, allR_eq, List.all_eq_true]
  intro c hc
  have hc' := List.mem_range.1 hc
  cases hb : Nat.beq (mactR M (Nat.succ c)) 0
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) (h (c + 1) (Nat.succ_pos c) (by omega))

theorem injR_of_sq {M : Nat} (e : mmulR M M = IDC) : injR M = true := by
  refine injR_of fun y hy hy64 h0 => ?_
  have h2 := mactR_mmulR M M y
  rw [e, mactR_IDC y hy64, h0, mactR_zero] at h2
  omega

theorem injR_of_pow4 {M : Nat} (e : powR M 4 = IDC) : injR M = true := by
  refine injR_of fun y hy hy64 h0 => ?_
  have h4 : mactR (powR M 4) y = mactR M (mactR M (mactR M (mactR M (mactR IDC y)))) := by
    rw [powR_succ, mactR_mmulR, powR_succ, mactR_mmulR, powR_succ, mactR_mmulR, powR_succ,
      mactR_mmulR]
    rfl
  rw [e, mactR_IDC y hy64, h0, mactR_zero, mactR_zero, mactR_zero] at h4
  omega

theorem invHyp_unpackL {M : Nat} (hM : M < 2 ^ 36) : invHyp (unpackL M) = invHypR M := by
  rw [invHyp, injC_unpackL, mmul_unpackL, idc_eq, beq_unpackL (mmulR_lt _ _) IDC_lt,
    show (unpackL M != unpackL IDC) = !(unpackL M == unpackL IDC) from rfl,
    beq_unpackL hM IDC_lt, invHypR]
  cases hq : Nat.beq (mmulR M M) IDC
  · cases Nat.beq (mactR M (fldR M 0)) 1 <;> cases injR M <;> rfl
  · have e : mmulR M M = IDC := Nat.eq_of_beq_eq_true hq
    have hc : Nat.beq (mactR M (fldR M 0)) 1 = true := by
      have := fldR_mmulR0 M M
      rw [e, fldR_IDC0] at this
      rw [← this]
      exact Nat.beq_refl 1
    rw [hc, injR_of_sq e]
    cases Nat.beq M IDC <;> rfl

theorem genHyp_unpackL {M : Nat} : genHyp (unpackL M) = genHypR M := by
  rw [genHyp, injC_unpackL, powC_unpackL, idc_eq, beq_unpackL (powR_lt _ _) IDC_lt, a0c_eq,
    mmul_unpackL, mmul_unpackL, mmul_unpackL, powC_unpackL, powC_unpackL,
    inZ_unpackL (powR_lt _ _), inZ_unpackL (powR_lt _ _), genHypR]
  cases hq : Nat.beq (powR M 4) IDC
  · cases Nat.beq (mactR M (mactR M (mactR M (fldR M 0)))) 1 <;> cases injR M <;> rfl
  · have e : powR M 4 = IDC := Nat.eq_of_beq_eq_true hq
    have hc : Nat.beq (mactR M (mactR M (mactR M (fldR M 0)))) 1 = true := by
      have h4 : fldR (powR M 4) 0 = mactR M (mactR M (mactR M (fldR M 0))) := by
        rw [powR_succ, fldR_mmulR0, powR_succ, fldR_mmulR0, powR_succ, fldR_mmulR0, powR_succ,
          fldR_mmulR0, show powR M 0 = IDC from rfl, fldR_IDC0, mactR_one]
      rw [e, fldR_IDC0] at h4
      rw [← h4]
      exact Nat.beq_refl 1
    rw [hc, injR_of_pow4 e]
    rfl

theorem omcR_eq_all : ∀ c < 64, omcR c = mactR OMC c := by decide +kernel

theorem omcR_eq {c : Nat} (hc : c < 64) : omcR c = mactR OMC c := omcR_eq_all c hc

theorem hcR_lt (c0 c2 c4 : Nat) (h0 : c0 < 64) (h2 : c2 < 64) (h4 : c4 < 64) :
    hcR c0 c2 c4 < 2 ^ 36 := by
  rw [hcR, omcR_eq h0, omcR_eq h2, omcR_eq h4]
  exact pk6_lt h0 (mactR_lt _ _) h2 (mactR_lt _ _) h4 (mactR_lt _ _)

theorem hc_eq (c0 c2 c4 : Nat) (h0 : c0 < 64) (h2 : c2 < 64) (h4 : c4 < 64) :
    hc c0 c2 c4 = unpackL (hcR c0 c2 c4) := by
  rw [hcR, omcR_eq h0, omcR_eq h2, omcR_eq h4,
    unpackL_pk6 h0 (mactR_lt _ _) h2 (mactR_lt _ _) h4 (mactR_lt _ _), hc, omc_eq,
    mact_unpackL, mact_unpackL, mact_unpackL]

theorem allR_spec {n : Nat} {f : Nat → Bool} (h : allR n f = true) : ∀ i < n, f i = true := by
  rw [allR_eq, List.all_eq_true] at h
  exact fun i hi => h i (List.mem_range.2 hi)

theorem omcR_lt {c : Nat} (hc : c < 64) : omcR c < 64 := by
  rw [omcR_eq hc]
  exact mactR_lt _ _

theorem mactR_hcR {c0 c2 c4 : Nat} (h0 : c0 < 64) (h2 : c2 < 64) (h4 : c4 < 64) :
    mactR (hcR c0 c2 c4) c0 = Nat.xor (invPR c0 c2) (invQR c0 c4) := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ :=
    fldR_pk6 h0 (omcR_lt h0) h2 (omcR_lt h2) h4 (omcR_lt h4)
  rw [mactR_hsel, hcR, e0, e1, e2, e3, e4, e5]
  exact Nat.xor_assoc _ _ _

theorem invQR_spec : ∀ c0 < 64, ∀ c4 < 64, bIf(Nat.beq (Nat.shiftRight c0 4) 0,
    Nat.beq (invQR c0 c4) 0, Nat.beq (invSolR c0 (invQR c0 c4)) c4) = true := by
  decide +kernel

theorem mactR_hcActR {c0 c2 c4 : Nat} (h0 : c0 < 64) (h2 : c2 < 64) (h4 : c4 < 64) (x : Nat) :
    mactR (hcR c0 c2 c4) x = hcActR c0 c2 c4 x := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ :=
    fldR_pk6 h0 (omcR_lt h0) h2 (omcR_lt h2) h4 (omcR_lt h4)
  rw [mactR_hsel, hcR, e0, e1, e2, e3, e4, e5]
  exact Nat.xor_assoc _ _ _

theorem hatPowR_zero (M : Nat) : powR M 0 = IDC := rfl

theorem inZR_fldR_lt {X : Nat} (h : inZR X = true) : fldR X 0 < 4 := by
  unfold inZR at h
  cases e1 : Nat.beq X IDC
  · cases e2 : Nat.beq X OMC
    · rw [e1, e2] at h
      have e : X = mmulR OMC OMC := Nat.eq_of_beq_eq_true h
      rw [e]
      decide +kernel
    · rw [Nat.eq_of_beq_eq_true e2]
      decide +kernel
  · rw [Nat.eq_of_beq_eq_true e1]
    decide +kernel

theorem hsel_crdR0 (x j v : Nat) : hselR (crdR x j) 0 v = hselR x (2 * j) v := by
  unfold hselR
  rw [hatBeq_bit, hatBeq_bit]
  have hb : (crdR x j).testBit 0 = x.testBit (2 * j) := by
    change ((x >>> (2 * j)) &&& 3).testBit 0 = _
    rw [Nat.testBit_and, Nat.testBit_shiftRight]
    simp
  rw [hb]

theorem hsel_crdR1 (x j v : Nat) : hselR (crdR x j) 1 v = hselR x (2 * j + 1) v := by
  unfold hselR
  rw [hatBeq_bit, hatBeq_bit]
  have hb : (crdR x j).testBit 1 = x.testBit (2 * j + 1) := by
    change ((x >>> (2 * j)) &&& 3).testBit 1 = _
    have h3 : Nat.testBit 3 1 = true := by decide
    rw [Nat.testBit_and, Nat.testBit_shiftRight, h3, Bool.and_true]
  rw [hb]

theorem hcActR_f4s (c0 c2 c4 x : Nat) : hcActR c0 c2 c4 x =
    Nat.xor (Nat.xor (f4sR (crdR x 0) c0) (f4sR (crdR x 1) c2)) (f4sR (crdR x 2) c4) := by
  unfold hcActR colPR invQR f4sR
  rw [hsel_crdR0, hsel_crdR1, hsel_crdR0, hsel_crdR1, hsel_crdR0, hsel_crdR1]
  change ((0 ^^^ hselR x 0 c0 ^^^ hselR x 1 (omcR c0)) ^^^ hselR x 2 c2 ^^^ hselR x 3 (omcR c2)) ^^^
      (hselR x 4 c4 ^^^ hselR x 5 (omcR c4)) =
    ((hselR x 0 c0 ^^^ hselR x 1 (omcR c0)) ^^^ (hselR x 2 c2 ^^^ hselR x 3 (omcR c2))) ^^^
      (hselR x 4 c4 ^^^ hselR x 5 (omcR c4))
  simp only [Nat.zero_xor, Nat.xor_assoc]

theorem crdR_xor (a b i : Nat) : crdR (Nat.xor a b) i = Nat.xor (crdR a i) (crdR b i) := by
  change ((a ^^^ b) >>> (2 * i)) &&& 3 = ((a >>> (2 * i)) &&& 3) ^^^ ((b >>> (2 * i)) &&& 3)
  apply Nat.eq_of_testBit_eq
  intro n
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight]
  cases (3 : Nat).testBit n <;> simp

theorem crdR_lt (v i : Nat) : crdR v i < 4 := by
  change (v >>> (2 * i)) &&& 3 < 4
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem hatXor64 {a b : Nat} (ha : a < 64) (hb : b < 64) : Nat.xor a b < 64 :=
  Nat.xor_lt_two_pow (n := 6) ha hb

theorem crdR_f4s_all : ∀ k < 4, ∀ c < 64, ∀ i < 3, crdR (f4sR k c) i = f4sR k (crdR c i) := by
  decide +kernel

theorem crdR_f4s {c : Nat} (k j i : Nat) (hc : c < 64) (hi : i < 3) :
    crdR (f4sR (crdR k j) c) i = f4sR (crdR k j) (crdR c i) :=
  crdR_f4s_all _ (crdR_lt _ _) c hc i hi

theorem f4sR_comm : ∀ a < 4, ∀ b < 4, f4sR a b = f4sR b a := by decide +kernel

theorem f4sR_sq_xor : ∀ a < 4, ∀ b < 4,
    f4sR (Nat.xor a b) (Nat.xor a b) = Nat.xor (f4sR a a) (f4sR b b) := by decide +kernel

theorem hatXorLt4 : ∀ k < 4, ∀ v < 4, Nat.xor k v < 4 := by decide +kernel

theorem hatFrob : ∀ t < 4,
    f4sR (f4sR t t) (f4sR t t) = 1 → t = 1 := by decide +kernel

theorem hatXor9 (A P Q E R I : Nat) :
    Nat.xor (Nat.xor (Nat.xor (Nat.xor A P) Q) (Nat.xor (Nat.xor P E) R)) (Nat.xor (Nat.xor Q R) I) =
      Nat.xor (Nat.xor A E) I := by
  change ((A ^^^ P) ^^^ Q) ^^^ ((P ^^^ E) ^^^ R) ^^^ ((Q ^^^ R) ^^^ I) = (A ^^^ E) ^^^ I
  apply Nat.eq_of_testBit_eq
  intro n
  simp only [Nat.testBit_xor]
  cases A.testBit n <;> cases P.testBit n <;> cases Q.testBit n <;> cases E.testBit n <;>
    cases R.testBit n <;> cases I.testBit n <;> rfl

@[expose] noncomputable def trCR (c0 c2 c4 : Nat) : Nat :=
  Nat.xor (Nat.xor (crdR c0 0) (crdR c2 1)) (crdR c4 2)

theorem trCR_sq {c0 c2 c4 : Nat} (h0 : c0 < 64) (h2 : c2 < 64) (h4 : c4 < 64) :
    trCR (hcActR c0 c2 c4 c0) (hcActR c0 c2 c4 c2) (hcActR c0 c2 c4 c4) =
      f4sR (trCR c0 c2 c4) (trCR c0 c2 c4) := by
  unfold trCR
  rw [hcActR_f4s c0 c2 c4 c0, hcActR_f4s c0 c2 c4 c2, hcActR_f4s c0 c2 c4 c4]
  simp only [crdR_xor, crdR_f4s _ _ _ h0 (by norm_num : 0 < 3), crdR_f4s _ _ _ h0 (by norm_num : 1 < 3),
    crdR_f4s _ _ _ h0 (by norm_num : 2 < 3), crdR_f4s _ _ _ h2 (by norm_num : 0 < 3),
    crdR_f4s _ _ _ h2 (by norm_num : 1 < 3), crdR_f4s _ _ _ h2 (by norm_num : 2 < 3),
    crdR_f4s _ _ _ h4 (by norm_num : 0 < 3), crdR_f4s _ _ _ h4 (by norm_num : 1 < 3),
    crdR_f4s _ _ _ h4 (by norm_num : 2 < 3)]
  have l := crdR_lt
  rw [f4sR_comm (crdR c2 0) (l _ _) (crdR c0 1) (l _ _),
    f4sR_comm (crdR c4 0) (l _ _) (crdR c0 2) (l _ _),
    f4sR_comm (crdR c4 1) (l _ _) (crdR c2 2) (l _ _),
    f4sR_sq_xor _ (hatXorLt4 _ (l c0 0) _ (l c2 1)) _ (l c4 2),
    f4sR_sq_xor _ (l c0 0) _ (l c2 1)]
  exact hatXor9 _ _ _ _ _ _

theorem omcR_xor_all : ∀ a < 64, ∀ b < 64, omcR (Nat.xor a b) = Nat.xor (omcR a) (omcR b) := by
  decide +kernel

theorem crdR_omc_all : ∀ v < 64, ∀ j < 3, crdR (omcR v) j = omcR (crdR v j) := by decide +kernel

theorem f4sR_omc_all : ∀ k < 4, ∀ v < 64, f4sR (omcR k) v = omcR (f4sR k v) := by decide +kernel

theorem f4sR_lt64 : ∀ k < 4, ∀ v < 64, f4sR k v < 64 := by decide +kernel

theorem hcActR_omc {c0 c2 c4 v : Nat} (h0 : c0 < 64) (h2 : c2 < 64) (h4 : c4 < 64)
    (hv : v < 64) : hcActR c0 c2 c4 (omcR v) = omcR (hcActR c0 c2 c4 v) := by
  have l := crdR_lt
  rw [hcActR_f4s, hcActR_f4s, crdR_omc_all v hv 0 (by norm_num), crdR_omc_all v hv 1 (by norm_num),
    crdR_omc_all v hv 2 (by norm_num), f4sR_omc_all _ (l _ _) _ h0, f4sR_omc_all _ (l _ _) _ h2,
    f4sR_omc_all _ (l _ _) _ h4,
    omcR_xor_all _ (hatXor64 (f4sR_lt64 _ (l _ _) _ h0) (f4sR_lt64 _ (l _ _) _ h2))
      _ (f4sR_lt64 _ (l _ _) _ h4),
    omcR_xor_all _ (f4sR_lt64 _ (l _ _) _ h0) _ (f4sR_lt64 _ (l _ _) _ h2)]

theorem hcActR_f4sR {c0 c2 c4 v : Nat} (h0 : c0 < 64) (h2 : c2 < 64) (h4 : c4 < 64)
    (hv : v < 64) (k : Nat) : hcActR c0 c2 c4 (f4sR k v) = f4sR k (hcActR c0 c2 c4 v) := by
  rw [← mactR_hcActR h0 h2 h4, ← mactR_hcActR h0 h2 h4, f4sR, f4sR, mactR_xor, mactR_hselR,
    mactR_hselR, mactR_hcActR h0 h2 h4, mactR_hcActR h0 h2 h4, hcActR_omc h0 h2 h4 hv]

theorem hcActR_lt {c0 c2 c4 : Nat} (h0 : c0 < 64) (h2 : c2 < 64) (h4 : c4 < 64) (x : Nat) :
    hcActR c0 c2 c4 x < 64 := by
  rw [← mactR_hcActR h0 h2 h4]
  exact mactR_lt _ _

theorem hcActR_sq {c0 c2 c4 : Nat} (h0 : c0 < 64) (h2 : c2 < 64) (h4 : c4 < 64) (y : Nat) :
    hcActR (hcActR c0 c2 c4 c0) (hcActR c0 c2 c4 c2) (hcActR c0 c2 c4 c4) y =
      hcActR c0 c2 c4 (hcActR c0 c2 c4 y) := by
  rw [hcActR_f4s (hcActR c0 c2 c4 c0), hcActR_f4s c0 c2 c4 y, ← mactR_hcActR h0 h2 h4
    (Nat.xor _ _), mactR_xor, mactR_xor, mactR_hcActR h0 h2 h4, mactR_hcActR h0 h2 h4,
    mactR_hcActR h0 h2 h4, hcActR_f4sR h0 h2 h4 h0, hcActR_f4sR h0 h2 h4 h2,
    hcActR_f4sR h0 h2 h4 h4]

theorem hatF4s01 (v : Nat) : f4sR 0 v = 0 ∧ f4sR 1 v = v := by
  refine ⟨?_, ?_⟩
  · change Nat.xor 0 0 = 0
    exact Nat.xor_zero 0
  · change Nat.xor v 0 = v
    exact Nat.xor_zero v

theorem hcActR_e {c0 c2 c4 : Nat} : hcActR c0 c2 c4 1 = c0 ∧ hcActR c0 c2 c4 4 = c2 ∧
    hcActR c0 c2 c4 16 = c4 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [hcActR_f4s]
  · change (f4sR 1 c0 ^^^ f4sR 0 c2) ^^^ f4sR 0 c4 = c0
    rw [(hatF4s01 c2).1, (hatF4s01 c4).1, (hatF4s01 c0).2, Nat.xor_zero, Nat.xor_zero]
  · change (f4sR 0 c0 ^^^ f4sR 1 c2) ^^^ f4sR 0 c4 = c2
    rw [(hatF4s01 c0).1, (hatF4s01 c4).1, (hatF4s01 c2).2, Nat.zero_xor, Nat.xor_zero]
  · change (f4sR 0 c0 ^^^ f4sR 0 c2) ^^^ f4sR 1 c4 = c4
    rw [(hatF4s01 c0).1, (hatF4s01 c2).1, (hatF4s01 c4).2, Nat.zero_xor, Nat.zero_xor]

theorem trCR_of_pow4 {c0 c2 c4 : Nat} (h0 : c0 < 64) (h2 : c2 < 64) (h4 : c4 < 64)
    (e : powR (hcR c0 c2 c4) 4 = IDC) : trCR c0 c2 c4 = 1 := by
  have hq : ∀ x < 64, hcActR c0 c2 c4 (hcActR c0 c2 c4 (hcActR c0 c2 c4 (hcActR c0 c2 c4 x))) =
      x := by
    intro x hx
    have h4' : mactR (powR (hcR c0 c2 c4) 4) x = mactR (hcR c0 c2 c4) (mactR (hcR c0 c2 c4)
        (mactR (hcR c0 c2 c4) (mactR (hcR c0 c2 c4) (mactR IDC x)))) := by
      rw [powR_succ, mactR_mmulR, powR_succ, mactR_mmulR, powR_succ, mactR_mmulR, powR_succ,
        mactR_mmulR]
      rfl
    rw [e, mactR_IDC x hx, mactR_hcActR h0 h2 h4, mactR_hcActR h0 h2 h4,
      mactR_hcActR h0 h2 h4, mactR_hcActR h0 h2 h4] at h4'
    exact h4'.symm
  have hd0 := hcActR_lt h0 h2 h4 c0
  have hd2 := hcActR_lt h0 h2 h4 c2
  have hd4 := hcActR_lt h0 h2 h4 c4
  have s1 := trCR_sq hd0 hd2 hd4
  rw [trCR_sq h0 h2 h4, hcActR_sq h0 h2 h4, hcActR_sq h0 h2 h4, hcActR_sq h0 h2 h4] at s1
  obtain ⟨e0, e2, e4⟩ := hcActR_e (c0 := c0) (c2 := c2) (c4 := c4)
  have q0 := hq 1 (by norm_num)
  have q2 := hq 4 (by norm_num)
  have q4 := hq 16 (by norm_num)
  rw [e0] at q0
  rw [e2] at q2
  rw [e4] at q4
  rw [q0, q2, q4] at s1
  exact hatFrob _ (hatXorLt4 _ (hatXorLt4 _ (crdR_lt _ _) _ (crdR_lt _ _)) _ (crdR_lt _ _)) s1.symm

theorem hatSq1 : ∀ t < 4, f4sR t t = 1 → t = 1 := by decide +kernel

theorem trCR_of_sq {c0 c2 c4 : Nat} (h0 : c0 < 64) (h2 : c2 < 64) (h4 : c4 < 64)
    (e : mmulR (hcR c0 c2 c4) (hcR c0 c2 c4) = IDC) : trCR c0 c2 c4 = 1 := by
  have hq : ∀ x < 64, hcActR c0 c2 c4 (hcActR c0 c2 c4 x) = x := by
    intro x hx
    have h2' := mactR_mmulR (hcR c0 c2 c4) (hcR c0 c2 c4) x
    rw [e, mactR_IDC x hx, mactR_hcActR h0 h2 h4, mactR_hcActR h0 h2 h4] at h2'
    exact h2'.symm
  have s1 := trCR_sq h0 h2 h4
  obtain ⟨e0, e2, e4⟩ := hcActR_e (c0 := c0) (c2 := c2) (c4 := c4)
  have q0 := hq 1 (by norm_num)
  have q2 := hq 4 (by norm_num)
  have q4 := hq 16 (by norm_num)
  rw [e0] at q0
  rw [e2] at q2
  rw [e4] at q4
  rw [q0, q2, q4] at s1
  exact hatSq1 _ (hatXorLt4 _ (hatXorLt4 _ (crdR_lt _ _) _ (crdR_lt _ _)) _ (crdR_lt _ _)) s1.symm

theorem c4_of_trCR {c0 c2 c4 : Nat} (h4 : c4 < 64) (ht : trCR c0 c2 c4 = 1) :
    c4 = Nat.add (c4 % 16) (Nat.mul 16 (trKR c0 c2)) := by
  have key : ∀ a < 4, ∀ b < 4, ∀ c < 64,
      Nat.xor (Nat.xor a b) (crdR c 2) = 1 → c = Nat.add (c % 16) (Nat.mul 16 (Nat.xor 1 (Nat.xor a b))) := by
    decide +kernel
  exact key _ (crdR_lt _ _) _ (crdR_lt _ _) c4 h4 ht

@[expose] def HatF4 := Fin 4

instance : DecidableEq HatF4 := inferInstanceAs (DecidableEq (Fin 4))
instance : Fintype HatF4 := inferInstanceAs (Fintype (Fin 4))
instance : Add HatF4 := ⟨fun a b =>
  (⟨(Nat.xor (a : Fin 4).val (b : Fin 4).val) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4)⟩
noncomputable instance : Mul HatF4 := ⟨fun a b =>
  (⟨(f4sR (a : Fin 4).val (b : Fin 4).val) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4)⟩
instance : Zero HatF4 := ⟨(⟨0, by decide⟩ : Fin 4)⟩
instance : One HatF4 := ⟨(⟨1, by decide⟩ : Fin 4)⟩
instance : Neg HatF4 := ⟨fun a => a⟩

noncomputable instance : CommRing HatF4 where
  add_assoc := by decide +kernel
  zero_add := by decide +kernel
  add_zero := by decide +kernel
  add_comm := by decide +kernel
  mul_assoc := by decide +kernel
  one_mul := by decide +kernel
  mul_one := by decide +kernel
  zero_mul := by decide +kernel
  mul_zero := by decide +kernel
  left_distrib := by decide +kernel
  right_distrib := by decide +kernel
  neg_add_cancel := by decide +kernel
  mul_comm := by decide +kernel
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : CharP HatF4 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero (by decide +kernel) (by decide +kernel)

def hatF4Of (n : Nat) : HatF4 := (⟨n % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4)

theorem hatF4Of_xor {a b : Nat} (ha : a < 4) (hb : b < 4) :
    hatF4Of (Nat.xor a b) = hatF4Of a + hatF4Of b := by
  apply Fin.ext
  change Nat.xor a b % 4 = Nat.xor (a % 4) (b % 4) % 4
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem hatF4Of_mul {a b : Nat} (ha : a < 4) (hb : b < 4) :
    hatF4Of (f4sR a b) = hatF4Of a * hatF4Of b := by
  apply Fin.ext
  change f4sR a b % 4 = f4sR (a % 4) (b % 4) % 4
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem hatF4Of_inj {a b : Nat} (ha : a < 4) (hb : b < 4) (h : hatF4Of a = hatF4Of b) : a = b := by
  have h' : a % 4 = b % 4 := congrArg (fun x : Fin 4 => x.val) h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'

theorem hatXor4lt {a b : Nat} (ha : a < 4) (hb : b < 4) : Nat.xor a b < 4 := hatXorLt4 a ha b hb

theorem hatF4sLt : ∀ a < 4, ∀ b < 4, f4sR a b < 4 := by decide +kernel

theorem hatF4sLt' {a b : Nat} (ha : a < 4) (hb : b < 4) : f4sR a b < 4 := hatF4sLt a ha b hb

def hatE2F {R : Type} [CommRing R] (a b c d e f g h k : R) : R :=
  a * e + b * d + a * k + c * g + e * k + f * h

theorem hatE2F_sq {R : Type} [CommRing R] [CharP R 2] (a b c d e f g h k : R) :
    hatE2F (a * a + d * b + g * c) (b * a + e * b + h * c) (c * a + f * b + k * c)
      (a * d + d * e + g * f) (b * d + e * e + h * f) (c * d + f * e + k * f)
      (a * g + d * h + g * k) (b * g + e * h + h * k) (c * g + f * h + k * k) =
      hatE2F a b c d e f g h k * hatE2F a b c d e f g h k := by
  unfold hatE2F
  grind

@[expose] noncomputable def e2NR (a b c d e f g h k : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (f4sR a e) (f4sR b d)) (f4sR a k)) (f4sR c g))
    (f4sR e k)) (f4sR f h)

theorem e2NR_sq {a b c d e f g h k : Nat} (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4)
    (he : e < 4) (hf : f < 4) (hg : g < 4) (hh : h < 4) (hk : k < 4) :
    e2NR (Nat.xor (Nat.xor (f4sR a a) (f4sR d b)) (f4sR g c))
      (Nat.xor (Nat.xor (f4sR b a) (f4sR e b)) (f4sR h c))
      (Nat.xor (Nat.xor (f4sR c a) (f4sR f b)) (f4sR k c))
      (Nat.xor (Nat.xor (f4sR a d) (f4sR d e)) (f4sR g f))
      (Nat.xor (Nat.xor (f4sR b d) (f4sR e e)) (f4sR h f))
      (Nat.xor (Nat.xor (f4sR c d) (f4sR f e)) (f4sR k f))
      (Nat.xor (Nat.xor (f4sR a g) (f4sR d h)) (f4sR g k))
      (Nat.xor (Nat.xor (f4sR b g) (f4sR e h)) (f4sR h k))
      (Nat.xor (Nat.xor (f4sR c g) (f4sR f h)) (f4sR k k)) =
      f4sR (e2NR a b c d e f g h k) (e2NR a b c d e f g h k) := by
  unfold e2NR
  apply hatF4Of_inj
    (by repeat (first | assumption | apply hatF4sLt' | apply hatXor4lt))
    (by repeat (first | assumption | apply hatF4sLt' | apply hatXor4lt))
  simp (disch := repeat (first | assumption | apply hatF4sLt' | apply hatXor4lt)) only
    [hatF4Of_xor, hatF4Of_mul]
  exact hatE2F_sq (hatF4Of a) (hatF4Of b) (hatF4Of c) (hatF4Of d) (hatF4Of e) (hatF4Of f)
    (hatF4Of g) (hatF4Of h) (hatF4Of k)

@[expose] noncomputable def e2CR (c0 c2 c4 : Nat) : Nat :=
  e2NR (crdR c0 0) (crdR c2 0) (crdR c4 0) (crdR c0 1) (crdR c2 1) (crdR c4 1) (crdR c0 2)
    (crdR c2 2) (crdR c4 2)

theorem e2CR_sq {c0 c2 c4 : Nat} (h0 : c0 < 64) (h2 : c2 < 64) (h4 : c4 < 64) :
    e2CR (hcActR c0 c2 c4 c0) (hcActR c0 c2 c4 c2) (hcActR c0 c2 c4 c4) =
      f4sR (e2CR c0 c2 c4) (e2CR c0 c2 c4) := by
  unfold e2CR
  rw [hcActR_f4s c0 c2 c4 c0, hcActR_f4s c0 c2 c4 c2, hcActR_f4s c0 c2 c4 c4]
  simp only [crdR_xor, crdR_f4s _ _ _ h0 (by norm_num : 0 < 3), crdR_f4s _ _ _ h0 (by norm_num : 1 < 3),
    crdR_f4s _ _ _ h0 (by norm_num : 2 < 3), crdR_f4s _ _ _ h2 (by norm_num : 0 < 3),
    crdR_f4s _ _ _ h2 (by norm_num : 1 < 3), crdR_f4s _ _ _ h2 (by norm_num : 2 < 3),
    crdR_f4s _ _ _ h4 (by norm_num : 0 < 3), crdR_f4s _ _ _ h4 (by norm_num : 1 < 3),
    crdR_f4s _ _ _ h4 (by norm_num : 2 < 3)]
  have l := crdR_lt
  exact e2NR_sq (l _ _) (l _ _) (l _ _) (l _ _) (l _ _) (l _ _) (l _ _) (l _ _) (l _ _)

theorem e2CR_lt (c0 c2 c4 : Nat) : e2CR c0 c2 c4 < 4 := by
  unfold e2CR e2NR
  repeat (first | apply hatF4sLt' | apply hatXor4lt | apply crdR_lt)

theorem e2CR_of_pow4 {c0 c2 c4 : Nat} (h0 : c0 < 64) (h2 : c2 < 64) (h4 : c4 < 64)
    (e : powR (hcR c0 c2 c4) 4 = IDC) : e2CR c0 c2 c4 = 1 := by
  have hq : ∀ x < 64, hcActR c0 c2 c4 (hcActR c0 c2 c4 (hcActR c0 c2 c4 (hcActR c0 c2 c4 x))) =
      x := by
    intro x hx
    have h4' : mactR (powR (hcR c0 c2 c4) 4) x = mactR (hcR c0 c2 c4) (mactR (hcR c0 c2 c4)
        (mactR (hcR c0 c2 c4) (mactR (hcR c0 c2 c4) (mactR IDC x)))) := by
      rw [powR_succ, mactR_mmulR, powR_succ, mactR_mmulR, powR_succ, mactR_mmulR, powR_succ,
        mactR_mmulR]
      rfl
    rw [e, mactR_IDC x hx, mactR_hcActR h0 h2 h4, mactR_hcActR h0 h2 h4,
      mactR_hcActR h0 h2 h4, mactR_hcActR h0 h2 h4] at h4'
    exact h4'.symm
  have hd0 := hcActR_lt h0 h2 h4 c0
  have hd2 := hcActR_lt h0 h2 h4 c2
  have hd4 := hcActR_lt h0 h2 h4 c4
  have s1 := e2CR_sq hd0 hd2 hd4
  rw [e2CR_sq h0 h2 h4, hcActR_sq h0 h2 h4, hcActR_sq h0 h2 h4, hcActR_sq h0 h2 h4] at s1
  obtain ⟨e0, e2, e4⟩ := hcActR_e (c0 := c0) (c2 := c2) (c4 := c4)
  have q0 := hq 1 (by norm_num)
  have q2 := hq 4 (by norm_num)
  have q4 := hq 16 (by norm_num)
  rw [e0] at q0
  rw [e2] at q2
  rw [e4] at q4
  rw [q0, q2, q4] at s1
  exact hatFrob _ (e2CR_lt _ _ _) s1.symm

theorem hatXorSw (A B D E F G : Nat) :
    Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor A B) D) E) F) G =
      Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor A B) D) F) E) G := by
  change ((((A ^^^ B) ^^^ D) ^^^ E) ^^^ F) ^^^ G = ((((A ^^^ B) ^^^ D) ^^^ F) ^^^ E) ^^^ G
  rw [Nat.xor_assoc _ E F, Nat.xor_comm E F, ← Nat.xor_assoc]

theorem e2CR_split {c0 c2 c4 : Nat} (h : crdR c4 2 = trKR c0 c2) :
    e2CR c0 c2 c4 = Nat.xor (Nat.xor (e2KR c0 c2) (f4sR (crdR c4 0) (crdR c0 2)))
      (f4sR (crdR c4 1) (crdR c2 2)) := by
  unfold e2CR e2NR e2KR
  rw [h]
  exact hatXorSw _ _ _ _ _ _

theorem e2KR_lt (c0 c2 : Nat) : e2KR c0 c2 < 4 := by
  unfold e2KR trKR
  repeat (first | apply hatF4sLt' | apply hatXor4lt | apply crdR_lt | decide)

theorem hatSolKeyB : ∀ z0 < 4, ∀ z1 < 4, ∀ C < 4, ∀ a < 4, ∀ b < 4,
    bIf(Nat.beq (Nat.add z0 z1) 0, true, bIf(Nat.beq (Nat.xor (Nat.xor C (f4sR a z0)) (f4sR b z1)) 1,
      Nat.beq (Nat.add a (Nat.mul 4 b)) (hatSolR z0 z1 C (nIf(Nat.beq z1 0, b, a))), true)) =
      true := by
  decide +kernel

theorem hatSolKey {z0 z1 C a b : Nat} (h0 : z0 < 4) (h1 : z1 < 4) (hC : C < 4) (ha : a < 4)
    (hb : b < 4) (hz : Nat.beq (Nat.add z0 z1) 0 = false)
    (he : Nat.xor (Nat.xor C (f4sR a z0)) (f4sR b z1) = 1) :
    Nat.add a (Nat.mul 4 b) = hatSolR z0 z1 C (nIf(Nat.beq z1 0, b, a)) := by
  have k := hatSolKeyB z0 h0 z1 h1 C hC a ha b hb
  rw [hz, he, Nat.beq_refl] at k
  exact Nat.eq_of_beq_eq_true k

theorem hatMod16 : ∀ c < 64, c % 16 = Nat.add (crdR c 0) (Nat.mul 4 (crdR c 1)) := by
  decide +kernel

theorem hatSelLt : ∀ z < 4, ∀ a < 4, ∀ b < 4, nIf(Nat.beq z 0, b, a) < 4 := by decide +kernel

theorem hatTrK : ∀ a < 4, ∀ b < 4, ∀ c < 4, Nat.xor (Nat.xor a b) c = 1 → c = Nat.xor 1 (Nat.xor a b) := by
  decide +kernel

theorem invCell_spec {L : List Nat} {c0 c2 : Nat} (h0 : c0 < 64) (h2 : c2 < 64)
    (h : invCellR L c0 c2 (invPR c0 c2) = true) : ∀ c4 < 64, invChkR L c0 c2 c4 = true := by
  intro c4 h4
  cases hh : invHypR (hcR c0 c2 c4)
  · unfold invChkR
    rw [hh]
  have hpre : Nat.xor (invPR c0 c2) (invQR c0 c4) = 1 := by
    have hh' := hh
    unfold invHypR at hh'
    have h1 := (bAnd_iff' hh').1
    have hf : fldR (hcR c0 c2 c4) 0 = c0 :=
      (fldR_pk6 h0 (omcR_lt h0) h2 (omcR_lt h2) h4 (omcR_lt h4)).1
    rw [hf, mactR_hcR h0 h2 h4] at h1
    exact Nat.eq_of_beq_eq_true h1
  have hq := invQR_spec c0 h0 c4 h4
  unfold invCellR at h
  cases hk : Nat.beq (Nat.shiftRight c0 4) 0
  · rw [hk] at hq h
    have hq' : invSolR c0 (invQR c0 c4) = c4 := Nat.eq_of_beq_eq_true hq
    have hx : Nat.xor (invPR c0 c2) 1 = invQR c0 c4 := by
      rw [← hpre]
      change invPR c0 c2 ^^^ (invPR c0 c2 ^^^ invQR c0 c4) = _
      rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    rw [hx, hq'] at h
    exact h
  · rw [hk] at hq h
    have hq' : invQR c0 c4 = 0 := Nat.eq_of_beq_eq_true hq
    rw [hq'] at hpre
    have hp : invPR c0 c2 = 1 := by
      rw [← hpre]
      exact (Nat.xor_zero _).symm
    rw [hp] at h
    have hc4 := c4_of_trCR h4 (trCR_of_sq h0 h2 h4
      (Nat.eq_of_beq_eq_true (bAnd_iff' (bAnd_iff' (by unfold invHypR at hh; exact hh)).2).1))
    have hc' := allR_spec (n := 16)
      (f := fun t => invChkR L c0 c2 (Nat.add t (Nat.mul 16 (trKR c0 c2)))) h (c4 % 16)
      (Nat.mod_lt _ (by norm_num))
    rw [← hc4] at hc'
    exact hc'

theorem hatA0act (x : Nat) : mactR A0C x = hcActR 42 4 45 x := by
  have e : A0C = hcR 42 4 45 := by decide +kernel
  rw [e]
  exact mactR_hcActR (by norm_num) (by norm_num) (by norm_num) x

theorem genCell_spec {L : List Nat} {c0 c2 : Nat} (h0 : c0 < 64) (h2 : c2 < 64)
    (h : genCellR L c0 c2 (invPR c0 c2) = true) : ∀ c4 < 64, genChkR L c0 c2 c4 = true := by
  intro c4 h4
  cases hh : genHypR (hcR c0 c2 c4)
  · unfold genChkR
    rw [hh]
  have ep : powR (hcR c0 c2 c4) 4 = IDC :=
    Nat.eq_of_beq_eq_true (bAnd_iff' (bAnd_iff' (by unfold genHypR at hh; exact hh)).2).1
  have ht := trCR_of_pow4 h0 h2 h4 ep
  have hc4 := c4_of_trCR h4 ht
  have hc' : genC4R L c0 c2 (invPR c0 c2) c4 = true := by
    unfold genCellR at h
    cases hz : Nat.beq (Nat.add (crdR c0 2) (crdR c2 2)) 0
    · rw [hz] at h
      have hK : crdR c4 2 = trKR c0 c2 :=
        hatTrK _ (crdR_lt _ _) _ (crdR_lt _ _) _ (crdR_lt _ _) ht
      have he := e2CR_of_pow4 h0 h2 h4 ep
      rw [e2CR_split hK] at he
      have hkey := hatSolKey (crdR_lt c0 2) (crdR_lt c2 2) (e2KR_lt c0 c2) (crdR_lt c4 0)
        (crdR_lt c4 1) hz he
      have hs : genC4R L c0 c2 (invPR c0 c2) (Nat.add (hatSolR (crdR c0 2) (crdR c2 2) (e2KR c0 c2)
          (nIf(Nat.beq (crdR c2 2) 0, crdR c4 1, crdR c4 0))) (Nat.mul 16 (trKR c0 c2))) = true :=
        allR_spec (n := 4) (f := fun s => genC4R L c0 c2 (invPR c0 c2)
          (Nat.add (hatSolR (crdR c0 2) (crdR c2 2) (e2KR c0 c2) s) (Nat.mul 16 (trKR c0 c2)))) h _
          (hatSelLt _ (crdR_lt _ _) _ (crdR_lt _ _) _ (crdR_lt _ _))
      rw [← hkey, ← hatMod16 c4 h4, ← hc4] at hs
      exact hs
    · rw [hz] at h
      have hs : genC4R L c0 c2 (invPR c0 c2) (Nat.add (c4 % 16) (Nat.mul 16 (trKR c0 c2))) =
          true :=
        allR_spec (n := 16) (f := fun t => genC4R L c0 c2 (invPR c0 c2)
          (Nat.add t (Nat.mul 16 (trKR c0 c2)))) h (c4 % 16) (Nat.mod_lt _ (by norm_num))
      rw [← hc4] at hs
      exact hs
  have hc : bIf(Nat.beq (genPreR c0 c2 (invPR c0 c2) c4) 1,
      bIf(Nat.blt (genPre3R c0 c2 c4) 4,
        bIf(Nat.beq (genPre2R c0 c2 c4) 4,
          bIf(Nat.blt (genPre5R c0 c2 c4) 4, memR (hcR c0 c2 c4) L, true), true), true), true) =
      true := hc'
  have hh' := hh
  unfold genHypR at hh'
  have hpre : genPreR c0 c2 (invPR c0 c2) c4 = 1 := by
    have h1 := (bAnd_iff' hh').1
    have hf : fldR (hcR c0 c2 c4) 0 = c0 :=
      (fldR_pk6 h0 (omcR_lt h0) h2 (omcR_lt h2) h4 (omcR_lt h4)).1
    rw [hf, mactR_hcActR h0 h2 h4, mactR_hcActR h0 h2 h4, mactR_hcActR h0 h2 h4] at h1
    exact Nat.eq_of_beq_eq_true h1
  have hpre2 : genPre2R c0 c2 c4 = 4 := by
    have e : powR (hcR c0 c2 c4) 4 = IDC :=
      Nat.eq_of_beq_eq_true (bAnd_iff' (bAnd_iff' hh').2).1
    have h4' : mactR (powR (hcR c0 c2 c4) 4) 4 = mactR (hcR c0 c2 c4) (mactR (hcR c0 c2 c4)
        (mactR (hcR c0 c2 c4) (mactR (hcR c0 c2 c4) (mactR IDC 4)))) := by
      rw [powR_succ, mactR_mmulR, powR_succ, mactR_mmulR, powR_succ, mactR_mmulR, powR_succ,
        mactR_mmulR]
      rfl
    rw [e, mactR_IDC 4 (by norm_num), mactR_hcActR h0 h2 h4, mactR_hcActR h0 h2 h4,
      mactR_hcActR h0 h2 h4, mactR_hcActR h0 h2 h4] at h4'
    exact h4'.symm
  have hpre3 : Nat.blt (genPre3R c0 c2 c4) 4 = true := by
    have hz := inZR_fldR_lt (bAnd_iff' (bAnd_iff' (bAnd_iff' hh').2).2).1
    have e : fldR (powR (mmulR A0C (hcR c0 c2 c4)) 5) 0 = genPre3R c0 c2 c4 := by
      rw [powR_succ, fldR_mmulR0, powR_succ, fldR_mmulR0, powR_succ, fldR_mmulR0, powR_succ,
        fldR_mmulR0, powR_succ, fldR_mmulR0, hatPowR_zero, fldR_IDC0, mactR_mmulR, mactR_mmulR, mactR_mmulR, mactR_mmulR, mactR_mmulR,
        mactR_hcActR h0 h2 h4, mactR_hcActR h0 h2 h4, mactR_hcActR h0 h2 h4,
        mactR_hcActR h0 h2 h4, mactR_hcActR h0 h2 h4]
      simp only [hatA0act]
      rfl
    rw [← e, Nat.blt_eq]
    exact hz
  have hpre5 : Nat.blt (genPre5R c0 c2 c4) 4 = true := by
    have hz := inZR_fldR_lt (bAnd_iff' (bAnd_iff' (bAnd_iff' hh').2).2).2
    have e : fldR (powR (mmulR A0C (mmulR (hcR c0 c2 c4) (hcR c0 c2 c4))) 5) 0 =
        genPre5R c0 c2 c4 := by
      simp only [powR_succ, fldR_mmulR0, hatPowR_zero, fldR_IDC0, mactR_mmulR,
        mactR_hcActR h0 h2 h4, hatA0act]
      rfl
    rw [← e, Nat.blt_eq]
    exact hz
  rw [hpre, Nat.beq_refl] at hc
  rw [hpre3] at hc
  rw [hpre2, Nat.beq_refl] at hc
  rw [hpre5] at hc
  unfold genChkR
  rw [hh]
  exact hc

theorem allCodes_of_slices {f : List Nat → Bool}
    (h : ∀ c0 < 64, ∀ c2 < 64, ∀ c4 < 64, f (unpackL (hcR c0 c2 c4)) = true) :
    allCodes f = true := by
  rw [allCodes, List.all_eq_true]
  intro c0 h0
  rw [List.all_eq_true]
  intro c2 h2
  rw [List.all_eq_true]
  intro c4 h4
  have h0' := List.mem_range.1 h0
  have h2' := List.mem_range.1 h2
  have h4' := List.mem_range.1 h4
  rw [hc_eq c0 c2 c4 h0' h2' h4']
  exact h c0 h0' c2 h2' c4 h4'

theorem slice_at {P : Nat → Nat → Nat → Bool} {lo : Nat}
    (h : allR 8 (fun i => allR 64 (fun c2 => allR 64 (fun c4 => P (Nat.add lo i) c2 c4))) =
      true) : ∀ i < 8, ∀ c2 < 64, ∀ c4 < 64, P (lo + i) c2 c4 = true :=
  fun i hi c2 h2 c4 h4 => allR_spec (allR_spec (allR_spec h i hi) c2 h2) c4 h4

theorem forall_c0_of_slices {P : Nat → Nat → Nat → Bool}
    (h : ∀ s < 8, ∀ i < 8, ∀ c2 < 64, ∀ c4 < 64, P (8 * s + i) c2 c4 = true) :
    ∀ c0 < 64, ∀ c2 < 64, ∀ c4 < 64, P c0 c2 c4 = true := by
  intro c0 h0 c2 h2 c4 h4
  have := h (c0 / 8) (by omega) (c0 % 8) (by omega) c2 h2 c4 h4
  rwa [Nat.div_add_mod] at this

theorem memR_eq (x : Nat) (L : List Nat) : memR x L = L.contains x := by
  induction L with
  | nil => rfl
  | cons y L ih =>
    change bIf(Nat.beq y x, true, memR x L) = _
    rw [ih, List.contains_cons]
    cases h : Nat.beq y x
    · have : (x == y) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        rw [e, Nat.beq_refl] at h
        exact Bool.false_ne_true h.symm
      rw [this, Bool.false_or]
    · have : (x == y) = true := by
        rw [Nat.eq_of_beq_eq_true h]
        exact beq_self_eq_true _
      rw [this, Bool.true_or]

theorem contains_unpackL {L : List Nat} (hL : ∀ y ∈ L, y < 2 ^ 36) {x : Nat} (hx : x < 2 ^ 36) :
    (L.map unpackL).contains (unpackL x) = memR x L := by
  rw [memR_eq]
  induction L with
  | nil => rfl
  | cons y L ih =>
    rw [List.map_cons, List.contains_cons, List.contains_cons,
      ih fun z hz => hL z (List.mem_cons_of_mem y hz), beq_unpackL hx (hL y List.mem_cons_self)]
    cases h : Nat.beq x y
    · have : (x == y) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        rw [e, Nat.beq_refl] at h
        exact Bool.false_ne_true h.symm
      rw [this]
    · have : (x == y) = true := by
        rw [Nat.eq_of_beq_eq_true h]
        exact beq_self_eq_true _
      rw [this]

theorem packL_lt {m : List Nat} (h : unpackL (packL m) = m) : packL m < 2 ^ 36 := by
  have e : ∀ k < 6, m.getD k 0 < 64 := by
    intro k hk
    rw [← h]
    interval_cases k <;> exact fldR_lt _ _
  exact pk6_lt (e 0 (by omega)) (e 1 (by omega)) (e 2 (by omega)) (e 3 (by omega))
    (e 4 (by omega)) (e 5 (by omega))

theorem fld36R_packBR : ∀ (G : List Nat), (∀ y ∈ G, y < 2 ^ 36) →
    ∀ j, fld36R (packBR G) j = G.getD j 0
  | [], _, j => by
    change (0 >>> (36 * j)) &&& (2 ^ 36 - 1) = 0
    simp
  | y :: G, hG, j => by
    have hy := hG y List.mem_cons_self
    have ih := fld36R_packBR G fun z hz => hG z (List.mem_cons_of_mem y hz)
    change ((y + 2 ^ 36 * packBR G) >>> (36 * j)) &&& (2 ^ 36 - 1) = (y :: G).getD j 0
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    cases j with
    | zero =>
      rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hy]
      rfl
    | succ j =>
      rw [List.getD_cons_succ, ← ih j]
      change _ = (packBR G >>> (36 * j)) &&& (2 ^ 36 - 1)
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.mul_succ, Nat.pow_add,
        Nat.mul_comm (2 ^ (36 * j)), ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hy, Nat.zero_add]

theorem contains_of_g0HitR {G : List Nat} (hG : ∀ y ∈ G, y < 2 ^ 36) {x j : Nat}
    (h : g0HitR (packBR G) G.length x j = true) : G.contains x = true := by
  obtain ⟨h1, h2⟩ := bAnd_iff' h
  have hj : j < G.length := Nat.le_of_ble_eq_true h1
  have e := Nat.eq_of_beq_eq_true h2
  rw [fld36R_packBR G hG, List.getD_eq_getElem _ _ hj] at e
  rw [← e]
  exact List.elem_eq_true_of_mem (List.getElem_mem hj)

theorem hatGenH (a b c : Nat) {A : Nat} (e : A = hcR a b c) (ha : a < 64) (hb : b < 64)
    (hc : c < 64) (M : Nat) : mmulR A M = mmulHR a b c M := by
  rw [e]
  unfold mmulR mmulHR
  simp only [mactR_hcActR ha hb hc]

theorem g0Walk_spec {G : List Nat} (hG : ∀ y ∈ G, y < 2 ^ 36) :
    ∀ (L W : List Nat), g0WalkR (packBR G) G.length L W = true → ∀ M ∈ L,
      (G.contains (mmulR (pk6 4 8 16 32 21 42) M) && G.contains (mmulR (pk6 16 32 4 8 57 30) M) &&
        G.contains (mmulR (pk6 21 42 1 2 4 8) M) &&
        G.contains (mmulR (pk6 27 45 4 8 1 2) M)) = true
  | [], _, _, M, hM => by simp at hM
  | y :: L, W, h, M, hM => by
    obtain ⟨hs, hw⟩ := bAnd_iff' (h : bAnd(g0StepR (packBR G) G.length y (W.headD 0),
      g0WalkR (packBR G) G.length L W.tail) = true)
    rcases List.mem_cons.1 hM with rfl | hM
    · obtain ⟨e1, hs⟩ := bAnd_iff' hs
      obtain ⟨e2, hs⟩ := bAnd_iff' hs
      obtain ⟨e3, e4⟩ := bAnd_iff' hs
      simp only [Bool.and_eq_true]
      have q1 : pk6 4 8 16 32 21 42 = hcR 4 16 21 := by decide +kernel
      have q2 : pk6 16 32 4 8 57 30 = hcR 16 4 57 := by decide +kernel
      have q3 : pk6 21 42 1 2 4 8 = hcR 21 1 4 := by decide +kernel
      have q4 : pk6 27 45 4 8 1 2 = hcR 27 4 1 := by decide +kernel
      rw [hatGenH 4 16 21 q1 (by norm_num) (by norm_num) (by norm_num),
        hatGenH 16 4 57 q2 (by norm_num) (by norm_num) (by norm_num),
        hatGenH 21 1 4 q3 (by norm_num) (by norm_num) (by norm_num),
        hatGenH 27 4 1 q4 (by norm_num) (by norm_num) (by norm_num)]
      exact ⟨⟨⟨contains_of_g0HitR hG e1, contains_of_g0HitR hG e2⟩, contains_of_g0HitR hG e3⟩,
        contains_of_g0HitR hG e4⟩
    · exact g0Walk_spec hG L W.tail hw M hM

theorem g0_core (L : List (List Nat)) (hwf : L.all (fun m => unpackL (packL m) == m) = true)
    (W : List Nat) (h : g0WR (L.map packL) W 1080 = true) : L.contains idc = true ∧
      L.all (fun m => L.contains (mmul g1c m) && L.contains (mmul g2c m) &&
        L.contains (mmul g1i m) && L.contains (mmul g2i m)) = true := by
  have hwf' : ∀ m ∈ L, unpackL (packL m) = m := by
    rw [List.all_eq_true] at hwf
    exact fun m hm => by simpa using hwf m hm
  have hG : (L.map packL).map unpackL = L := by
    rw [List.map_map]
    exact (List.map_congr_left fun m hm => hwf' m hm).trans (List.map_id _)
  have hlt : ∀ y ∈ L.map packL, y < 2 ^ 36 := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hy
    exact packL_lt (hwf' m hm)
  have hc : ∀ x, x < 2 ^ 36 → L.contains (unpackL x) = memR x (L.map packL) := by
    intro x hx
    have := contains_unpackL hlt hx
    rwa [hG] at this
  have g1 : g1c = unpackL (pk6 4 8 16 32 21 42) := by
    rw [unpackL_pk6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    rfl
  have g2 : g2c = unpackL (pk6 16 32 4 8 57 30) := by
    rw [unpackL_pk6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    rfl
  have g3 : g1i = unpackL (pk6 21 42 1 2 4 8) := by
    rw [unpackL_pk6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    rfl
  have g4 : g2i = unpackL (pk6 27 45 4 8 1 2) := by
    rw [unpackL_pk6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    rfl
  obtain ⟨h1, h'⟩ := bAnd_iff' h
  obtain ⟨hn, hw⟩ := bAnd_iff' h'
  rw [← Nat.eq_of_beq_eq_true hn] at hw
  refine ⟨by rw [idc_eq, hc _ IDC_lt]; exact h1, ?_⟩
  rw [List.all_eq_true]
  intro m hm
  have hm' := hwf' m hm
  rw [← hm', g1, g2, g3, g4, mmul_unpackL, mmul_unpackL, mmul_unpackL, mmul_unpackL,
    hc _ (mmulR_lt _ _), hc _ (mmulR_lt _ _), hc _ (mmulR_lt _ _), hc _ (mmulR_lt _ _),
    memR_eq, memR_eq, memR_eq, memR_eq]
  exact g0Walk_spec hlt _ W hw (packL m) (List.mem_map.2 ⟨m, hm, rfl⟩)

theorem g0OK_of_g0WR (hwf : g0List.all (fun m => unpackL (packL m) == m) = true)
    (hlen : g0List.length = 1080) (W : List Nat) (h : g0WR (g0List.map packL) W 1080 = true) :
    g0OK = true := by
  obtain ⟨h1, h2⟩ := g0_core g0List hwf W h
  unfold g0OK
  rw [h1, hlen, h2]
  rfl

theorem getD_unpackL_lt (A : Nat) {k : Nat} (hk : k < 6) : (unpackL A).getD k 0 < 64 := by
  interval_cases k <;> exact fldR_lt _ _

theorem invOK_of_mem
    (hwf : invTab.all (fun e => unpackL (packL e.1) == e.1 && unpackL (packL e.2.1) == e.2.1 &&
      unpackL (packL e.2.2) == e.2.2) = true)
    (hok : invTab.all (fun e => invEntR (packL e.1) (packL e.2.1) (packL e.2.2)) = true)
    {K : Nat} (hK : (invTab.map fun e => packL e.1).contains K = true) :
    invOK (unpackL K) = true := by
  obtain ⟨⟨k, a, b⟩, he, hk⟩ := List.mem_map.1 (List.mem_of_elem_eq_true hK)
  have hw := List.all_eq_true.1 hwf _ he
  have ho := List.all_eq_true.1 hok _ he
  simp only [Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨⟨w1, w2⟩, w3⟩ := hw
  obtain ⟨o1, o⟩ := bAnd_iff' ho
  obtain ⟨o2, o⟩ := bAnd_iff' o
  obtain ⟨o3, o4⟩ := bAnd_iff' o
  replace o1 := Nat.eq_of_beq_eq_true o1
  replace o2 := Nat.eq_of_beq_eq_true o2
  replace o3 := Nat.eq_of_beq_eq_true o3
  replace o4 := Nat.eq_of_beq_eq_true o4
  change packL k = K at hk
  change unpackL (packL k) = k at w1
  change unpackL (packL a) = a at w2
  change unpackL (packL b) = b at w3
  change mmulR (packL a) (packL b) = IDC at o1
  change mmulR (packL b) (packL a) = IDC at o2
  change mmulR (packL a) OMC = mmulR OMC (packL a) at o3
  change mmulR (packL a) (mmulR A0C (packL b)) = packL k at o4
  rw [hk] at w1 o4
  generalize packL a = A at w2 o1 o2 o3 o4
  generalize packL b = B at w3 o1 o2 o4
  subst w1 w2 w3
  unfold invOK
  rw [List.any_eq_true]
  refine ⟨_, he, ?_⟩
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨beq_self_eq_true _, ?_⟩, ?_⟩, ?_⟩
  · unfold pairB
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨fun c hc => ⟨?_, ?_⟩, fun k hk => getD_unpackL_lt A hk,
      fun k hk => getD_unpackL_lt B hk⟩, rfl⟩, rfl⟩
    · rw [mact_unpackL, mact_unpackL, ← mactR_mmulR, o1, mactR_IDC c hc]
    · rw [mact_unpackL, mact_unpackL, ← mactR_mmulR, o2, mactR_IDC c hc]
  · rw [beq_iff_eq, omc_eq, mmul_unpackL, mmul_unpackL, o3]
  · rw [beq_iff_eq, a0c_eq, mmul_unpackL, mmul_unpackL, o4]

theorem inv_of_slices (L : List Nat)
    (hwf : invTab.all (fun e => unpackL (packL e.1) == e.1 && unpackL (packL e.2.1) == e.2.1 &&
      unpackL (packL e.2.2) == e.2.2) = true)
    (hok : invTab.all (fun e => invEntR (packL e.1) (packL e.2.1) (packL e.2.2)) = true)
    (hL : invTab.map (fun e => packL e.1) = L)
    (h : ∀ s < 8, invSliceR L (8 * s) 8 = true) :
    allCodes (fun m => !invHyp m || invOK m) = true := by
  refine allCodes_of_slices (forall_c0_of_slices fun s hs i hi c2 h2 c4 h4 => ?_)
  have hc0 : 8 * s + i < 64 := by omega
  have hcell : invCellR L (8 * s + i) c2 (invPR (8 * s + i) c2) = true :=
    allR_spec (allR_spec (h s hs) i hi) c2 h2
  have hsl := invCell_spec hc0 h2 hcell c4 h4
  unfold invChkR at hsl
  rw [invHyp_unpackL (hcR_lt (8 * s + i) c2 c4 hc0 h2 h4)]
  cases hh : invHypR (hcR (8 * s + i) c2 c4)
  · rfl
  · rw [hh] at hsl
    rw [invOK_of_mem hwf hok (by rw [hL, ← memR_eq]; exact hsl)]
    rfl

theorem gencR_eq (j : Nat) : genc j = unpackL (gencR j) := by
  unfold genc gencR
  by_cases h0 : j = 0
  · subst h0
    decide +kernel
  · have e0 : Nat.beq j 0 = false := by
      cases h : Nat.beq j 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) h0
    simp only [h0, e0, ↓reduceIte]
    by_cases h1 : j = 1
    · subst h1
      decide +kernel
    · have e1 : Nat.beq j 1 = false := by
        cases h : Nat.beq j 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) h1
      simp only [h1, e1, ↓reduceIte]
      decide +kernel

theorem hatWval_eq : ∀ w : List Nat, wval w = unpackL (wvalR w)
  | [] => idc_eq
  | j :: w => by
    change mmul (genc j) (wval w) = unpackL (mmulR (gencR j) (wvalR w))
    rw [gencR_eq, hatWval_eq w, mmul_unpackL]

theorem conjOK_of_ent
    (hcw : conjTab.all (fun c => unpackL (packL c.1) == c.1 && unpackL (packL c.2.1) == c.2.1) =
      true)
    (hok : conjTab.all conjEntR = true) : conjOK = true := by
  unfold conjOK
  rw [List.all_eq_true] at hcw hok ⊢
  rintro ⟨k, a, w⟩ he
  have hw := hcw _ he
  have ho := hok _ he
  simp only [Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨w1, w2⟩ := hw
  unfold conjEntR at ho
  simp only [Bool.and_eq_true] at ho
  obtain ⟨⟨⟨o1, o2⟩, o3⟩, o4⟩ := ho
  replace o1 := Nat.eq_of_beq_eq_true o1
  replace o2 := Nat.eq_of_beq_eq_true o2
  replace o3 := Nat.eq_of_beq_eq_true o3
  change unpackL (packL k) = k at w1
  change unpackL (packL a) = a at w2
  change mmulR (packL k) (packL a) = IDC at o1
  change mmulR (packL a) (packL k) = IDC at o2
  change wvalR w = mmulR (packL a) (mmulR A0C (packL k)) at o3
  change w.all (· < 2) = true at o4
  generalize packL k = A at w1 o1 o2 o3
  generalize packL a = B at w2 o1 o2 o3
  subst w1 w2
  change (pairB (unpackL A) (unpackL B) && wval w == mmul (unpackL B) (mmul a0c (unpackL A)) &&
    w.all (· < 2)) = true
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, o4⟩
  · unfold pairB
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨fun c hc => ⟨?_, ?_⟩, fun k hk => getD_unpackL_lt A hk,
      fun k hk => getD_unpackL_lt B hk⟩, rfl⟩, rfl⟩
    · rw [mact_unpackL, mact_unpackL, ← mactR_mmulR, o1, mactR_IDC c hc]
    · rw [mact_unpackL, mact_unpackL, ← mactR_mmulR, o2, mactR_IDC c hc]
  · rw [beq_iff_eq, hatWval_eq, a0c_eq, mmul_unpackL, mmul_unpackL, o3]

theorem hatGenOK_of_mem
    (hwf : genTab.all (fun e => unpackL (packL e.1) == e.1) = true)
    (hcw : conjTab.all (fun c => unpackL (packL c.1) == c.1 && unpackL (packL c.2.1) == c.2.1) =
      true)
    (hok : genTab.all genEntR = true)
    {K : Nat} (hK : (genTab.map fun e => packL e.1).contains K = true) :
    genOK (unpackL K) = true := by
  obtain ⟨⟨k, i, w⟩, he, hk⟩ := List.mem_map.1 (List.mem_of_elem_eq_true hK)
  have hw : unpackL (packL k) = k := by simpa using List.all_eq_true.1 hwf _ he
  have ho := List.all_eq_true.1 hok _ he
  change packL k = K at hk
  unfold genEntR at ho
  dsimp only at ho
  rw [hk] at hw ho
  subst hw
  unfold genOK
  rw [List.any_eq_true]
  refine ⟨_, he, ?_⟩
  cases hc : conjTab[i]? with
  | none =>
    rw [hc] at ho
    exact absurd ho Bool.false_ne_true
  | some c =>
    obtain ⟨c1, c21, cw⟩ := c
    have hcw' := List.all_eq_true.1 hcw _ (List.mem_of_getElem? hc)
    simp only [Bool.and_eq_true, beq_iff_eq] at hcw'
    obtain ⟨e1, e2⟩ := hcw'
    simp only [hc, Bool.and_eq_true] at ho
    obtain ⟨o1, o2⟩ := ho
    replace o1 := Nat.eq_of_beq_eq_true o1
    simp only [Bool.and_eq_true]
    refine ⟨beq_self_eq_true _, ?_, o2⟩
    rw [beq_iff_eq, hatWval_eq, ← e1, ← e2, mmul_unpackL, mmul_unpackL, o1]

theorem gen_of_slices (L : List Nat)
    (hwf : genTab.all (fun e => unpackL (packL e.1) == e.1) = true)
    (hcw : conjTab.all (fun c => unpackL (packL c.1) == c.1 && unpackL (packL c.2.1) == c.2.1) =
      true)
    (hok : genTab.all genEntR = true)
    (hL : genTab.map (fun e => packL e.1) = L)
    (h : ∀ s < 8, ∃ k, genSliceR (L.drop k) (8 * s) 8 = true) :
    allCodes (fun m => !genHyp m || genOK m) = true := by
  refine allCodes_of_slices (forall_c0_of_slices fun s hs i hi c2 h2 c4 h4 => ?_)
  have hc0 : 8 * s + i < 64 := by omega
  obtain ⟨k, hk⟩ := h s hs
  have hcell : genCellR (L.drop k) (8 * s + i) c2 (invPR (8 * s + i) c2) = true :=
    allR_spec (allR_spec hk i hi) c2 h2
  have hsl := genCell_spec hc0 h2 hcell c4 h4
  unfold genChkR at hsl
  rw [genHyp_unpackL]
  cases hh : genHypR (hcR (8 * s + i) c2 c4)
  · rfl
  · rw [hh] at hsl
    have hm : memR (hcR (8 * s + i) c2 c4) L = true := by
      rw [memR_eq] at hsl ⊢
      exact List.elem_iff.2 (List.mem_of_mem_drop (List.elem_iff.1 hsl))
    rw [hatGenOK_of_mem hwf hcw hok (by rw [hL, ← memR_eq]; exact hm)]
    rfl

end CFSG.KC.HatA6

end
