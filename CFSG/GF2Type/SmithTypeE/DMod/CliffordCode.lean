module

public import CFSG.GF2Type.SmithTypeE.DMod.Clifford
public import Certificates.Data.Kernel.SmithD6.Clifford

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6

theorem foldl_xor_acc (f : ℕ → ℕ) (L : List ℕ) (a : ℕ) :
    L.foldl (fun acc i => acc ^^^ f i) a = a ^^^ L.foldl (fun acc i => acc ^^^ f i) 0 := by
  induction L generalizing a with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldl_cons]
    rw [ih (a ^^^ f x), ih (0 ^^^ f x), Nat.zero_xor, Nat.xor_assoc]

theorem xorFold_zero (f : ℕ → ℕ) : xorFold 0 f = 0 := rfl

theorem xorFold_succ (n : ℕ) (f : ℕ → ℕ) : xorFold (n + 1) f = xorFold n f ^^^ f n := by
  unfold xorFold
  rw [List.range_succ, List.foldl_append]
  rfl

theorem xorFold_xor (n : ℕ) (f g : ℕ → ℕ) :
    xorFold n (fun i => f i ^^^ g i) = xorFold n f ^^^ xorFold n g := by
  induction n with
  | zero => simp [xorFold_zero]
  | succ n ih =>
    rw [xorFold_succ, xorFold_succ, xorFold_succ, ih]
    ac_rfl

theorem xorFold_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) :
    xorFold n f = xorFold n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorFold_succ, xorFold_succ, ih fun i hi => h i (by omega), h n (by omega)]

theorem map_xorFold {F : ℕ → ℕ} (hF : ∀ a b, F (a ^^^ b) = F a ^^^ F b) (n : ℕ) (f : ℕ → ℕ) :
    F (xorFold n f) = xorFold n (fun i => F (f i)) := by
  have h0 : F 0 = 0 := by
    have := hF 0 0
    rw [Nat.xor_self] at this
    rw [this, Nat.xor_self]
  induction n with
  | zero => exact h0
  | succ n ih => rw [xorFold_succ, xorFold_succ, hF, ih]

theorem testBit_xorFold_bits (s n j : ℕ) :
    (xorFold n fun k => bif s.testBit k then 2 ^ k else 0).testBit j =
      (decide (j < n) && s.testBit j) := by
  induction n with
  | zero => simp [xorFold_zero]
  | succ n ih =>
    rw [xorFold_succ, Nat.testBit_xor, ih]
    by_cases hj : j < n
    · have h1 : j < n + 1 := by omega
      have h2 : n ≠ j := by omega
      cases hs : s.testBit n <;> simp [hj, h1, h2, Nat.testBit_two_pow]
    · by_cases hjn : j = n
      · subst hjn
        cases hs : s.testBit j <;> simp [hj, hs, Nat.testBit_two_pow]
      · have h1 : ¬ j < n + 1 := by omega
        have h2 : n ≠ j := by omega
        cases hs : s.testBit n <;> simp [hj, h1, h2, Nat.testBit_two_pow]

theorem xorFold_bits {s n : ℕ} (hs : s < 2 ^ n) :
    xorFold n (fun k => bif s.testBit k then 2 ^ k else 0) = s := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_xorFold_bits]
  by_cases hj : j < n
  · simp [hj]
  · have : s.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hj, this]

theorem eq_of_xor_of_two_pow {F G : ℕ → ℕ} (hF : ∀ a b, F (a ^^^ b) = F a ^^^ F b)
    (hG : ∀ a b, G (a ^^^ b) = G a ^^^ G b) {n : ℕ} (h : ∀ k < n, F (2 ^ k) = G (2 ^ k))
    {s : ℕ} (hs : s < 2 ^ n) : F s = G s := by
  have hF0 : F 0 = 0 := by
    have := hF 0 0
    rw [Nat.xor_self] at this
    rw [this, Nat.xor_self]
  have hG0 : G 0 = 0 := by
    have := hG 0 0
    rw [Nat.xor_self] at this
    rw [this, Nat.xor_self]
  rw [← xorFold_bits hs, map_xorFold hF, map_xorFold hG]
  refine xorFold_congr fun k hk => ?_
  cases s.testBit k
  · exact hF0.trans hG0.symm
  · exact h k hk

theorem xor_and_distrib (a b m : ℕ) : (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> cases m.testBit j <;> rfl

theorem xor_shiftLeft (a b k : ℕ) : (a ^^^ b) <<< k = (a <<< k) ^^^ (b <<< k) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_shiftLeft, Nat.testBit_xor]
  cases decide (j ≥ k) <;> simp

theorem xor_shiftRight (a b k : ℕ) : (a ^^^ b) >>> k = (a >>> k) ^^^ (b >>> k) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_shiftRight, Nat.testBit_xor]

theorem wedC_xor (i a b : ℕ) : wedC i (a ^^^ b) = wedC i a ^^^ wedC i b := by
  unfold wedC
  rw [xor_and_distrib, xor_shiftLeft]

theorem contrC_xor (i a b : ℕ) : contrC i (a ^^^ b) = contrC i a ^^^ contrC i b := by
  unfold contrC
  rw [xor_and_distrib, xor_shiftRight]

theorem cond_xor (c : Bool) (a b : ℕ) :
    (bif c then a ^^^ b else 0) = (bif c then a else 0) ^^^ (bif c then b else 0) := by
  cases c <;> simp

theorem rhoC_xor (x a b : ℕ) : rhoC x (a ^^^ b) = rhoC x a ^^^ rhoC x b := by
  unfold rhoC
  simp only [wedC_xor, contrC_xor, cond_xor, xorFold_xor]
  ac_rfl

theorem termC_xor (t : ℕ × ℕ × Bool) (a b : ℕ) : termC t (a ^^^ b) = termC t a ^^^ termC t b := by
  unfold termC
  cases t.2.2
  · simp only [cond_false, xor_and_distrib, xor_shiftRight]
  · simp only [cond_true, xor_and_distrib, xor_shiftLeft]

theorem rhoT_xor (ts : List (ℕ × ℕ × Bool)) (a b : ℕ) :
    rhoT ts (a ^^^ b) = rhoT ts a ^^^ rhoT ts b := by
  induction ts with
  | nil => simp [rhoT]
  | cons t ts ih =>
    simp only [rhoT, List.foldr_cons] at ih ⊢
    rw [ih, termC_xor]
    ac_rfl

theorem rhoT_eq_of_rhoTOK {u w : ℕ} {ts : List (ℕ × ℕ × Bool)} (h : rhoTOK u w ts = true)
    {s : ℕ} (hs : s < 2 ^ 64) : rhoT ts s = rhoC u (rhoC w s) := by
  simp only [rhoTOK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine eq_of_xor_of_two_pow (G := fun s => rhoC u (rhoC w s)) (rhoT_xor ts)
    (fun a b => ?_) h hs
  rw [rhoC_xor, rhoC_xor]

@[expose] def decode64 (c : ℕ) : W64 := fun T => bit (c.testBit T.val)

theorem decode64_apply (c : ℕ) (T : Fin 64) : decode64 c T = bit (c.testBit T.val) := rfl

theorem decode64_xor (a b : ℕ) : decode64 (a ^^^ b) = decode64 a + decode64 b := by
  funext T
  simp only [decode64_apply, Pi.add_apply, Nat.testBit_xor, bit_xor]

theorem decode64_zero : decode64 0 = 0 := by
  funext T
  simp [decode64_apply, bit]

theorem decode64_two_pow (T : Fin 64) : decode64 (2 ^ T.val) = Pi.single T 1 := by
  funext S
  rw [decode64_apply, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : S = T
  · subst h
    simp [bit]
  · have : T.val ≠ S.val := fun e => h (Fin.ext e.symm)
    simp [h, this, bit]

theorem decode64_xorFold (n : ℕ) (f : ℕ → ℕ) :
    decode64 (xorFold n f) = ∑ i ∈ Finset.range n, decode64 (f i) := by
  induction n with
  | zero => simp [xorFold_zero, decode64_zero]
  | succ n ih => rw [xorFold_succ, decode64_xor, ih, Finset.sum_range_succ]

theorem wed_mask_facts : ∀ T : Fin 64, ∀ i : Fin 6,
    (decide (T.val ≥ 2 ^ i.val) && (outMask i.val).testBit (T.val - 2 ^ i.val)) =
      T.val.testBit i.val ∧
    (T.val.testBit i.val = true → T.val - 2 ^ i.val = T.val ^^^ 2 ^ i.val) := by
  decide

theorem contr_mask_facts : ∀ T : Fin 64, ∀ i : Fin 6,
    (inMask i.val).testBit (2 ^ i.val + T.val) = !T.val.testBit i.val ∧
    (T.val.testBit i.val = false → 2 ^ i.val + T.val = T.val ^^^ 2 ^ i.val) := by
  decide

theorem testBit_wedC (i : Fin 6) (s : ℕ) (T : Fin 64) :
    (wedC i.val s).testBit T.val = (T.val.testBit i.val && s.testBit (flipS i T).val) := by
  obtain ⟨h1, h2⟩ := wed_mask_facts T i
  unfold wedC
  rw [Nat.testBit_shiftLeft, Nat.testBit_and, flipS_val]
  cases hT : T.val.testBit i.val
  · rw [hT] at h1
    cases hd : decide (T.val ≥ 2 ^ i.val)
    · rfl
    · rw [hd, Bool.true_and] at h1
      rw [h1]
      simp
  · rw [hT] at h1
    rw [← h2 hT]
    cases hd : decide (T.val ≥ 2 ^ i.val)
    · rw [hd, Bool.false_and] at h1
      exact absurd h1 (by decide)
    · rw [hd, Bool.true_and] at h1
      rw [h1]
      simp

theorem testBit_contrC (i : Fin 6) (s : ℕ) (T : Fin 64) :
    (contrC i.val s).testBit T.val = (!T.val.testBit i.val && s.testBit (flipS i T).val) := by
  obtain ⟨h1, h2⟩ := contr_mask_facts T i
  unfold contrC
  rw [Nat.testBit_shiftRight, Nat.testBit_and, h1, flipS_val]
  cases hT : T.val.testBit i.val
  · rw [h2 hT]
    simp
  · simp

theorem decode64_wedC (i : Fin 6) (s : ℕ) :
    decode64 (wedC i.val s) = wedgeL i (decode64 s) := by
  funext T
  rw [decode64_apply, testBit_wedC, wedgeL_apply, decode64_apply]
  cases T.val.testBit i.val <;> simp [bit]

theorem decode64_contrC (i : Fin 6) (s : ℕ) :
    decode64 (contrC i.val s) = contrL i (decode64 s) := by
  funext T
  rw [decode64_apply, testBit_contrC, contrL_apply, decode64_apply]
  cases T.val.testBit i.val <;> simp [bit]

theorem decode64_rhoC (x s : ℕ) : decode64 (rhoC x s) = rhoL (dec12 x) (decode64 s) := by
  unfold rhoC
  rw [decode64_xor, decode64_xorFold, decode64_xorFold, rhoL_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.sum_apply,
    ← Fin.sum_univ_eq_sum_range (fun i => decode64 (bif x.testBit i then wedC i s else 0)) 6,
    ← Fin.sum_univ_eq_sum_range
      (fun i => decode64 (bif x.testBit (6 + i) then contrC i s else 0)) 6]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply]
    change _ = (if x.testBit i.val then (1 : ZMod 2) else 0) • _
    cases x.testBit i.val
    · simp [decode64_zero]
    · simp [decode64_wedC]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply]
    change _ = (if x.testBit (6 + i.val) then (1 : ZMod 2) else 0) • _
    cases x.testBit (6 + i.val)
    · simp [decode64_zero]
    · simp [decode64_contrC]

theorem decode64_liftT {u w : ℕ} {ts : List (ℕ × ℕ × Bool)} (h : rhoTOK u w ts = true)
    {s : ℕ} (hs : s < 2 ^ 64) :
    decode64 (liftT ts s) = tlift (dec12 u) (dec12 w) (decode64 s) := by
  unfold liftT
  rw [rhoT_eq_of_rhoTOK h hs, decode64_xor, decode64_rhoC, decode64_rhoC]
  rfl

end CFSG.GF2Type.SmithTypeE.DMod
