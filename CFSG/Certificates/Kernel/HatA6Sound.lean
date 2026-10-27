module

public import Certificates.Data.Kernel.HatA6K

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
    (hd : d < 64) (he : e < 64) (hf : f < 64) :
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
    show ¬ j < 24 by omega, show ¬ j < 30 by omega, if_false]
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
  · simp only [h1, h2, h3, h4, h5, if_false, show ¬ j - 30 < 6 by omega, decide_false,
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

theorem sel_eq (M c n : Nat) (hn : n < 6) :
    (if c.testBit n = true then (unpackL M).getD n 0 else 0) =
      nIf(Nat.beq (Nat.land (Nat.shiftRight c n) 1) 1, fldR M n, 0) := by
  have hb : Nat.beq (Nat.land (Nat.shiftRight c n) 1) 1 = c.testBit n := by
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
  change (mactR M (c + 1) != 0) = _
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
    rw [hc]
    cases injR M <;> cases Nat.beq M IDC <;> rfl

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
    rw [hc]
    cases injR M <;> rfl

theorem hcR_lt (c0 c2 c4 : Nat) (h0 : c0 < 64) (h2 : c2 < 64) (h4 : c4 < 64) :
    hcR c0 c2 c4 < 2 ^ 36 :=
  pk6_lt h0 (mactR_lt _ _) h2 (mactR_lt _ _) h4 (mactR_lt _ _)

theorem hc_eq (c0 c2 c4 : Nat) (h0 : c0 < 64) (h2 : c2 < 64) (h4 : c4 < 64) :
    hc c0 c2 c4 = unpackL (hcR c0 c2 c4) := by
  rw [hcR, unpackL_pk6 h0 (mactR_lt _ _) h2 (mactR_lt _ _) h4 (mactR_lt _ _), hc, omc_eq,
    mact_unpackL, mact_unpackL, mact_unpackL]

theorem allR_spec {n : Nat} {f : Nat → Bool} (h : allR n f = true) : ∀ i < n, f i = true := by
  rw [allR_eq, List.all_eq_true] at h
  exact fun i hi => h i (List.mem_range.2 hi)

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

theorem inv_of_slices
    (h : ∀ s < 8, invSliceR (8 * s) 8 = true) :
    allCodes (fun m => !invHyp m || invOK m) = true := by
  refine allCodes_of_slices (forall_c0_of_slices fun s hs i hi c2 h2 c4 h4 => ?_)
  have hsl := slice_at (P := fun c0 c2 c4 => bIf(invHypR (hcR c0 c2 c4),
    invOK (unpackL (hcR c0 c2 c4)), true)) (lo := 8 * s) (h s hs) i hi c2 h2 c4 h4
  have hlt := hcR_lt (8 * s + i) c2 c4 (by omega) h2 h4
  rw [invHyp_unpackL hlt]
  cases hh : invHypR (hcR (8 * s + i) c2 c4)
  · rfl
  · rw [hh] at hsl
    simpa using hsl

theorem gen_of_slices
    (h : ∀ s < 8, genSliceR (8 * s) 8 = true) :
    allCodes (fun m => !genHyp m || genOK m) = true := by
  refine allCodes_of_slices (forall_c0_of_slices fun s hs i hi c2 h2 c4 h4 => ?_)
  have hsl := slice_at (P := fun c0 c2 c4 => bIf(genHypR (hcR c0 c2 c4),
    genOK (unpackL (hcR c0 c2 c4)), true)) (lo := 8 * s) (h s hs) i hi c2 h2 c4 h4
  rw [genHyp_unpackL]
  cases hh : genHypR (hcR (8 * s + i) c2 c4)
  · rfl
  · rw [hh] at hsl
    simpa using hsl

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

theorem g0_core (L : List (List Nat)) (hwf : L.all (fun m => unpackL (packL m) == m) = true)
    (h : g0R (L.map packL) = true) : L.contains idc = true ∧
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
  unfold g0R at h
  have h' := (bAnd_iff' h)
  refine ⟨by rw [idc_eq, hc _ IDC_lt]; exact h'.1, ?_⟩
  rw [List.all_eq_true]
  intro m hm
  have hm' := hwf' m hm
  rw [← hm', g1, g2, g3, g4, mmul_unpackL, mmul_unpackL, mmul_unpackL, mmul_unpackL,
    hc _ (mmulR_lt _ _), hc _ (mmulR_lt _ _), hc _ (mmulR_lt _ _), hc _ (mmulR_lt _ _)]
  have key : ∀ (L' : List Nat), List.rec (motive := fun _ => Bool) true (fun M _ ih =>
      bAnd(memR (mmulR (pk6 4 8 16 32 21 42) M) (L.map packL),
        bAnd(memR (mmulR (pk6 16 32 4 8 57 30) M) (L.map packL),
        bAnd(memR (mmulR (pk6 21 42 1 2 4 8) M) (L.map packL),
        bAnd(memR (mmulR (pk6 27 45 4 8 1 2) M) (L.map packL), ih))))) L' = true →
      ∀ M ∈ L', (memR (mmulR (pk6 4 8 16 32 21 42) M) (L.map packL) &&
        memR (mmulR (pk6 16 32 4 8 57 30) M) (L.map packL) &&
        memR (mmulR (pk6 21 42 1 2 4 8) M) (L.map packL) &&
        memR (mmulR (pk6 27 45 4 8 1 2) M) (L.map packL)) = true := by
    intro L'
    induction L' with
    | nil => intro _ M hM; simp at hM
    | cons y L' ih =>
      intro hL M hM
      have e1 := bAnd_iff' hL
      have e2 := bAnd_iff' e1.2
      have e3 := bAnd_iff' e2.2
      have e4 := bAnd_iff' e3.2
      rcases List.mem_cons.1 hM with rfl | hM
      · simp [e1.1, e2.1, e3.1, e4.1]
      · exact ih e4.2 M hM
  exact key _ h'.2 (packL m) (List.mem_map.2 ⟨m, hm, rfl⟩)

theorem g0OK_of_g0R (hwf : g0List.all (fun m => unpackL (packL m) == m) = true)
    (hlen : g0List.length = 1080) (h : g0R (g0List.map packL) = true) : g0OK = true := by
  obtain ⟨h1, h2⟩ := g0_core g0List hwf h
  unfold g0OK
  rw [h1, hlen, h2]
  rfl

end CFSG.KC.HatA6

end
