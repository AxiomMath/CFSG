module

public import Certificates.Data.Kernel.J2H2.Echelon
public import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

namespace CFSG.KC.J2H2

open CFSG.KD.J2H2 CFSG.KC.Enum CFSG.KS

theorem testBit_one' (b : Nat) : (1 : Nat).testBit b = decide (b = 0) := by
  rw [show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
  cases b <;> simp

theorem testBit_ite01 (c : Bool) (b : Nat) :
    (if c = true then 1 else 0 : Nat).testBit b = (c && decide (b = 0)) := by
  cases c
  · simp
  · simp [testBit_one']

theorem fld1_eq (R o : Nat) : Nat.land (Nat.shiftRight R o) 1 = if R.testBit o then 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  change ((R >>> o) &&& 1).testBit b = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_one', testBit_ite01]
  by_cases hb : b = 0
  · subst hb
    simp
  · simp [hb]

theorem testBit_fldw (V o w b : Nat) :
    (Nat.land (Nat.shiftRight V o) (Nat.sub (Nat.shiftLeft 1 w) 1)).testBit b =
      (V.testBit (o + b) && decide (b < w)) := by
  change ((V >>> o) &&& ((1 <<< w) - 1)).testBit b = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

theorem testBit_hvR (R j t r : Nat) :
    (hvR R j t).testBit r = (decide (r < 12) && R.testBit (384 * t + (32 * r + j))) := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0 (fun r ih => Nat.lor ih (Nat.shiftLeft
      fld(R, Nat.add (Nat.mul 384 t) (Nat.add (Nat.mul 32 r) j), 1) r)) n : Nat).testBit r =
      (decide (r < n) && R.testBit (384 * t + (32 * r + j))) := by
    intro n
    induction n with
    | zero =>
      change (0 : Nat).testBit r = _
      simp
    | succ n ih =>
      change (_ ||| _ <<< n : Nat).testBit r = _
      rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft, fld1_eq, testBit_ite01]
      by_cases h : r < n
      · have h1 : r < n + 1 := by omega
        have h2 : ¬ n ≤ r := by omega
        simp [h, h1, h2]
      · by_cases h' : r = n
        · subst h'
          simp
        · have h1 : ¬ r < n + 1 := by omega
          have h3 : r - n ≠ 0 := by omega
          simp [h, h1, h3]
  exact key 12

theorem testBit_fieldAt (V h b : Nat) :
    (fieldAt V h).testBit b = (V.testBit (384 * h + b) && decide (b < 384)) :=
  testBit_fldw V (Nat.mul 384 h) 384 b

theorem hvR_zero_of (R j t : Nat) (h : ∀ r < 12, R.testBit (384 * t + (32 * r + j)) = false) :
    hvR R j t = 0 := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_hvR, Nat.zero_testBit]
  by_cases hr : r < 12
  · simp [hr, h r hr]
  · simp [hr]

theorem hvR_zero_of_fieldAt {R t j : Nat} (h : fieldAt R t = 0) (hj : j < 30) : hvR R j t = 0 := by
  refine hvR_zero_of R j t fun r hr => ?_
  have e := congrArg (fun z => Nat.testBit z (32 * r + j)) h
  simp only [testBit_fieldAt, Nat.zero_testBit] at e
  have hb : 32 * r + j < 384 := by omega
  simpa [hb] using e

theorem hvR_zero_left (j t : Nat) : hvR 0 j t = 0 :=
  hvR_zero_of 0 j t fun _ _ => Nat.zero_testBit _

theorem beq_true {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem listK_spec {w m T : Nat} : ∀ {L : List Nat} {o n : Nat}, listK w m T L o n = true →
    o + L.length = n ∧ ∀ i < L.length, pg w m T (o + i) = L.getD i 0
  | [], o, n, h => by
    refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    have := beq_true h
    simpa using this
  | a :: L, o, n, h => by
    change bAnd(Nat.beq (pg w m T o) a, listK w m T L (Nat.succ o) n) = true at h
    rw [PK.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨e, hL⟩ := listK_spec h2
    refine ⟨by simp only [List.length_cons] at e ⊢; omega, fun i hi => ?_⟩
    cases i with
    | zero => simpa using beq_true h1
    | succ i =>
      have hi' : i < L.length := by simp only [List.length_cons] at hi; omega
      have := hL i hi'
      rw [List.getD_cons_succ, ← this]
      congr 1
      omega

@[expose] noncomputable def freeL (HP : Nat) (F : List Nat) (o : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i 30)
    (fun f _ ih i => bAnd(Nat.blt f 4608,
      bAnd(allN 30 (fun j => Nat.beq (bitF HP j f) (nIf(Nat.beq i j, 1, 0))), ih (Nat.succ i)))) F o

theorem freeL_spec {HP : Nat} : ∀ {F : List Nat} {o : Nat}, freeL HP F o = true →
    ∀ i < F.length, F.getD i 0 < 4608 ∧ ∀ j < 30, bitF HP j (F.getD i 0) = if o + i = j then 1 else 0
  | [], _, _ => fun i hi => absurd hi (Nat.not_lt_zero _)
  | f :: F, o, h => by
    change bAnd(Nat.blt f 4608, bAnd(allN 30 (fun j => Nat.beq (bitF HP j f) (nIf(Nat.beq o j, 1, 0))),
      freeL HP F (Nat.succ o))) = true at h
    simp only [PK.bAnd_eq, Bool.and_eq_true, PK.allN_iff, Nat.blt_eq, PK.nIf_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    intro i hi
    cases i with
    | zero =>
      refine ⟨by simpa using h1, fun j hj => ?_⟩
      have := beq_true (h2 j hj)
      simp only [List.getD_cons_zero, Nat.add_zero]
      rw [this]
      by_cases hoj : o = j
      · subst hoj
        simp [Nat.beq_refl]
      · have : Nat.beq o j = false := by
          cases hb : Nat.beq o j
          · rfl
          · exact absurd (beq_true hb) hoj
        simp [hoj, this]
    | succ i =>
      have hi' : i < F.length := by simp only [List.length_cons] at hi; omega
      obtain ⟨a, b⟩ := freeL_spec h3 i hi'
      refine ⟨by simpa using a, fun j hj => ?_⟩
      rw [List.getD_cons_succ, b j hj]
      congr 1
      simp only [Nat.succ_eq_add_one, eq_iff_iff]
      omega

theorem testBit_eN (b : Nat) : eN.testBit b = decide (b % 13 = 0 ∧ b / 13 < 12) := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0
      (fun r ih => Nat.lor ih (Nat.shiftLeft 1 (Nat.mul 13 r))) n : Nat).testBit b =
      decide (b % 13 = 0 ∧ b / 13 < n) := by
    intro n
    induction n with
    | zero =>
      change (0 : Nat).testBit b = _
      simp
    | succ n ih =>
      change (_ ||| 1 <<< (13 * n) : Nat).testBit b = _
      rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
  exact key 12

theorem testBit_unitF {k x β r : Nat} (hr : r < 12) :
    (unitF k x).testBit (12 * β + r) = decide (β = 12 * (128 * k + x) + r) := by
  change (eN <<< (144 * (128 * k + x))).testBit (12 * β + r) = _
  rw [Nat.testBit_shiftLeft, testBit_eN, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem testBit_bitsF (F : List Nat) (b : Nat) :
    (List.rec (motive := fun _ => Nat) 0 (fun f _ ih => Nat.lor (Nat.shiftLeft 1 (Nat.mul 12 f)) ih)
      F : Nat).testBit b = decide (∃ f ∈ F, b = 12 * f) := by
  induction F with
  | nil =>
    change (0 : Nat).testBit b = _
    simp
  | cons f F ih =>
    change ((1 <<< (12 * f)) ||| _ : Nat).testBit b = _
    rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

theorem testBit_treeBits (GP PP b : Nat) : ∀ n, (Nat.rec (motive := fun _ => Nat) 0 (fun i ih => Nat.lor ih
      (Nat.rec (motive := fun _ => Nat) 0 (fun r ih2 => Nat.lor ih2 (Nat.shiftLeft 1 (Nat.mul 12
        (Nat.add (Nat.mul 12 (Nat.add (Nat.mul 128 (pg 2 3 GP (Nat.succ i))) (pg 7 127 PP (Nat.succ i)))) r))))
        12)) n : Nat).testBit b = true →
      ∃ i < n, ∃ r < 12, b = 12 * (12 * (128 * pg 2 3 GP (i + 1) + pg 7 127 PP (i + 1)) + r) := by
  have inner : ∀ c m, (Nat.rec (motive := fun _ => Nat) 0 (fun r ih2 => Nat.lor ih2
      (Nat.shiftLeft 1 (Nat.mul 12 (Nat.add (Nat.mul 12 c) r)))) m : Nat).testBit b = true →
      ∃ r < m, b = 12 * (12 * c + r) := by
    intro c m
    induction m with
    | zero =>
      intro h
      change (0 : Nat).testBit b = true at h
      simp at h
    | succ m ih =>
      intro h
      change (_ ||| 1 <<< (12 * (12 * c + m)) : Nat).testBit b = true at h
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨r, hr, e⟩ := ih h
        exact ⟨r, by omega, e⟩
      · exact ⟨m, by omega, (of_decide_eq_true h).symm⟩
  intro n
  induction n with
  | zero =>
    intro h
    change (0 : Nat).testBit b = true at h
    simp at h
  | succ n ih =>
    intro h
    change (_ ||| _ : Nat).testBit b = true at h
    rw [Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨i, hi, r, hr, e⟩ := ih h
      exact ⟨i, by omega, r, hr, e⟩
    · obtain ⟨r, hr, e⟩ := inner _ 12 h
      exact ⟨n, by omega, r, hr, e⟩

theorem conjL_spec {E : Nat → Nat} {g : Nat} : ∀ {Q : List Nat}, conjL E g Q = true →
    ∀ e ∈ Q, e < 16384 ∧
      Nat.beq (pcomp 315 9 511 g (E (e % 128))) (pcomp 315 9 511 (E (e / 128)) g) = true
  | [], _ => fun e he => absurd he List.not_mem_nil
  | e :: Q, h => by
    change bAnd(Nat.blt e 16384,
      bAnd(Nat.beq (pcomp 315 9 511 g (E (Nat.land e 127))) (pcomp 315 9 511 (E (Nat.shiftRight e 7)) g),
        conjL E g Q)) = true at h
    simp only [PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · have e1 : Nat.land x 127 = x % 128 := Nat.and_two_pow_sub_one_eq_mod x 7
      have e2 : Nat.shiftRight x 7 = x / 128 := Nat.shiftRight_eq_div_pow x 7
      rw [e1, e2] at h2
      exact ⟨h1, h2⟩
    · exact conjL_spec h3 x hx

end CFSG.KC.J2H2

end
