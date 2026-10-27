module

public import Certificates.Data.Kernel.Misc.G24
public import Mathlib.Data.Matrix.Mul
import CFSG.Certificates.Kernel.Spor.PK.MiscBase
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.Misc.Spec

open CFSG.KC.Misc.G24 (mulF2 oneF2)

@[expose] def pkMat (n x : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => if x.testBit (n * i.val + j.val) then 1 else 0

theorem pos_unique {n i j i' j' : ℕ} (hj : j < n) (hj' : j' < n)
    (h : n * i + j = n * i' + j') : i = i' ∧ j = j' := by
  have hn : 0 < n := by omega
  have h1 := congrArg (· / n) h
  have h2 := congrArg (· % n) h
  simp only [Nat.mul_add_div hn, Nat.mul_add_mod, Nat.div_eq_of_lt hj, Nat.div_eq_of_lt hj',
    Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at h1 h2
  omega

@[expose] def repu (s m : ℕ) : ℕ := ∑ t ∈ Finset.range m, 2 ^ (s * t)

theorem repu_lt {s : ℕ} (hs : 0 < s) (m : ℕ) : repu s m < 2 ^ (s * m) := by
  induction m with
  | zero => simp [repu]
  | succ m ih =>
    have h1 : repu s (m + 1) = repu s m + 2 ^ (s * m) := Finset.sum_range_succ _ _
    have h2 : 2 ^ (s * (m + 1)) = 2 ^ (s * m) * 2 ^ s := by rw [Nat.mul_succ, Nat.pow_add]
    have h3 : 2 ≤ 2 ^ s := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) hs
    have h4 := Nat.mul_le_mul_left (2 ^ (s * m)) h3
    omega

theorem testBit_repu {s : ℕ} (hs : 0 < s) (m q : ℕ) :
    (repu s m).testBit q = true ↔ ∃ t < m, q = s * t := by
  induction m with
  | zero => simp [repu]
  | succ m ih =>
    have h1 : repu s (m + 1) = repu s m + 2 ^ (s * m) := Finset.sum_range_succ _ _
    have h2 : repu s m + 2 ^ (s * m) = 2 ^ (s * m) * 1 ||| repu s m := by
      rw [Nat.add_comm, ← Nat.two_pow_add_eq_or_of_lt (repu_lt hs m) 1, Nat.mul_one]
    rw [h1, h2, Nat.testBit_or, Bool.or_eq_true, Nat.mul_one, Nat.testBit_two_pow,
      decide_eq_true_iff, ih]
    constructor
    · rintro (h | ⟨t, ht, h⟩)
      · exact ⟨m, by omega, h.symm⟩
      · exact ⟨t, by omega, h⟩
    · rintro ⟨t, ht, h⟩
      by_cases htm : t = m
      · exact Or.inl (by rw [← htm]; exact h.symm)
      · exact Or.inr ⟨t, by omega, h⟩

theorem repu_mul (s m : ℕ) : (2 ^ s - 1) * repu s m + 1 = 2 ^ (s * m) := by
  induction m with
  | zero => simp [repu]
  | succ m ih =>
    have h1 : repu s (m + 1) = repu s m + 2 ^ (s * m) := Finset.sum_range_succ _ _
    obtain ⟨q, hq⟩ : ∃ q, 2 ^ s = q + 1 :=
      ⟨2 ^ s - 1, by have := Nat.one_le_two_pow (n := s); omega⟩
    rw [h1, Nat.mul_succ, Nat.pow_add, hq, Nat.add_sub_cancel]
    rw [hq, Nat.add_sub_cancel] at ih
    calc q * (repu s m + 2 ^ (s * m)) + 1 = (q * repu s m + 1) + q * 2 ^ (s * m) := by ring
      _ = 2 ^ (s * m) + q * 2 ^ (s * m) := by rw [ih]
      _ = 2 ^ (s * m) * (q + 1) := by ring

theorem repu_eq {s : ℕ} (hs : 0 < s) (m : ℕ) : repu s m = (2 ^ (s * m) - 1) / (2 ^ s - 1) := by
  have h2 : 2 ≤ 2 ^ s := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) hs
  have h := repu_mul s m
  have h3 : 2 ^ (s * m) - 1 = (2 ^ s - 1) * repu s m := by omega
  rw [h3, Nat.mul_div_cancel_left _ (by omega)]

theorem blockSum_lt {n : ℕ} {f : ℕ → ℕ} (m : ℕ) (hf : ∀ t < m, f t < 2 ^ n) :
    ∑ t ∈ Finset.range m, f t * 2 ^ (n * t) < 2 ^ (n * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := ih (fun t ht => hf t (by omega))
    have h2 : f m < 2 ^ n := hf m (by omega)
    rw [Finset.sum_range_succ]
    have e : 2 ^ (n * (m + 1)) = 2 ^ n * 2 ^ (n * m) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    have h3 : (f m + 1) * 2 ^ (n * m) ≤ 2 ^ n * 2 ^ (n * m) := Nat.mul_le_mul_right _ h2
    rw [e]
    rw [Nat.add_mul, Nat.one_mul] at h3
    omega

theorem testBit_blockSum {n : ℕ} {f : ℕ → ℕ} (m : ℕ) (hf : ∀ t < m, f t < 2 ^ n) (i j : ℕ)
    (hj : j < n) :
    (∑ t ∈ Finset.range m, f t * 2 ^ (n * t)).testBit (n * i + j) =
      (decide (i < m) && (f i).testBit j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hS := blockSum_lt m (fun t ht => hf t (by omega))
    have hfm : f m < 2 ^ n := hf m (by omega)
    rw [Finset.sum_range_succ]
    have e : (∑ t ∈ Finset.range m, f t * 2 ^ (n * t)) + f m * 2 ^ (n * m) =
        2 ^ (n * m) * f m + ∑ t ∈ Finset.range m, f t * 2 ^ (n * t) := by ring
    rw [e, Nat.testBit_two_pow_mul_add _ hS]
    by_cases hi : i < m
    · have h1 : n * i + j < n * m := by
        have := Nat.mul_le_mul_left n (show i + 1 ≤ m by omega)
        rw [Nat.mul_succ] at this
        omega
      rw [if_pos h1, ih (fun t ht => hf t (by omega))]
      simp [hi, show i < m + 1 by omega]
    · obtain ⟨d, rfl⟩ : ∃ d, i = m + d := ⟨i - m, by omega⟩
      have h1 : ¬ n * (m + d) + j < n * m := by
        have := Nat.mul_le_mul_left n (show m ≤ m + d by omega)
        omega
      rw [if_neg h1]
      have e1 : n * (m + d) + j - n * m = n * d + j := by
        rw [Nat.mul_add]
        omega
      rw [e1]
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp
      · have h2 : n ≤ n * d + j := by
          have := Nat.mul_le_mul_left n hd
          omega
        have h3 : (f m).testBit (n * d + j) = false :=
          Nat.testBit_lt_two_pow
            (Nat.lt_of_lt_of_le hfm (Nat.pow_le_pow_right (by omega) h2))
        rw [h3]
        have h4 : ¬ m + d < m + 1 := by omega
        simp [h4]

theorem shl1_eq (n : ℕ) : Nat.shiftLeft 1 n = 2 ^ n := by
  have h := Nat.shiftLeft_eq 1 n
  rw [Nat.one_mul] at h
  exact h

@[expose] def stepF2 (n A B k : ℕ) : ℕ :=
  (((A >>> k) &&& repu n n) * (2 ^ n - 1)) &&& (((B >>> (n * k)) &&& (2 ^ n - 1)) * repu n n)

@[expose] def foldF2 (n A B : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => foldF2 n A B m ^^^ stepF2 n A B m

theorem mulF2_eq_fold {n : ℕ} (hn : 0 < n) (A B : ℕ) : mulF2 n A B = foldF2 n A B n := by
  have hR : (2 ^ (n * n) - 1) / (2 ^ n - 1) = repu n n := (repu_eq hn n).symm
  have key : ∀ m, Nat.rec (motive := fun _ => ℕ) 0
      (fun k acc => acc ^^^ ((((A >>> k) &&& ((2 ^ (n * n) - 1) / (2 ^ n - 1))) * (2 ^ n - 1)) &&&
        (((B >>> (n * k)) &&& (2 ^ n - 1)) * ((2 ^ (n * n) - 1) / (2 ^ n - 1))))) m =
      foldF2 n A B m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      show Nat.rec (motive := fun _ => ℕ) 0 _ m ^^^ _ = foldF2 n A B m ^^^ stepF2 n A B m
      rw [ih, stepF2, hR]
  rw [← key n]
  unfold mulF2
  simp only [CFSG.KS.PK.letN_eq, shl1_eq]
  rfl

theorem oneF2_eq (n : ℕ) : oneF2 n = repu (n + 1) n := by
  rw [repu_eq (Nat.succ_pos n) n]
  unfold oneF2
  simp only [shl1_eq]
  show (2 ^ (n * (n + 1)) - 1) / (2 ^ (n + 1) - 1) = _
  rw [Nat.mul_comm n (n + 1)]

theorem testBit_repu_block {n : ℕ} (hn : 0 < n) {i j : ℕ} (hj : j < n) :
    (repu n n).testBit (n * i + j) = decide (i < n ∧ j = 0) := by
  rw [Bool.eq_iff_iff, testBit_repu hn, decide_eq_true_iff]
  constructor
  · rintro ⟨t, ht, h⟩
    obtain ⟨h1, h2⟩ := pos_unique hj hn (i' := t) (j' := 0) (by omega)
    exact ⟨by omega, h2⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨i, hi, by omega⟩

theorem and_repu_eq {n : ℕ} (hn : 0 < n) (A k : ℕ) :
    (A >>> k) &&& repu n n =
      ∑ t ∈ Finset.range n, (if A.testBit (n * t + k) then 1 else 0) * 2 ^ (n * t) := by
  apply Nat.eq_of_testBit_eq
  intro q
  obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < n ∧ q = n * i + j :=
    ⟨q / n, q % n, Nat.mod_lt _ hn, (Nat.div_add_mod q n).symm⟩
  have hc : ∀ t < n, (if A.testBit (n * t + k) then 1 else 0) < 2 ^ n := by
    intro t _
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    split <;> omega
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_blockSum n hc i j hj,
    testBit_repu_block hn hj]
  by_cases hi : i < n
  · by_cases hj0 : j = 0
    · subst hj0
      cases hb : A.testBit (n * i + k)
      · simp [hi, hb, Nat.add_comm k]
      · simp [hi, hb, Nat.add_comm k]
    · have h1 : (if A.testBit (n * i + k) then 1 else 0).testBit j = false := by
        split
        · rw [Bool.eq_false_iff]
          intro h
          exact hj0 (Nat.testBit_one_eq_true_iff_self_eq_zero.mp h)
        · simp
      simp [hi, hj0, h1]
  · simp [hi]

theorem testBit_stepF2 {n : ℕ} (hn : 0 < n) (A B k : ℕ) {i j : ℕ} (hj : j < n) :
    (stepF2 n A B k).testBit (n * i + j) =
      (decide (i < n) && (A.testBit (n * i + k) && B.testBit (n * k + j))) := by
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hF : 2 ^ n - 1 < 2 ^ n := by omega
  set V := (B >>> (n * k)) &&& (2 ^ n - 1) with hV
  have hVlt : V < 2 ^ n := Nat.and_lt_two_pow _ hF
  have e1 : (((A >>> k) &&& repu n n) * (2 ^ n - 1)) =
      ∑ t ∈ Finset.range n, ((if A.testBit (n * t + k) then 1 else 0) * (2 ^ n - 1)) *
        2 ^ (n * t) := by
    rw [and_repu_eq hn, Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => Nat.mul_right_comm _ _ _
  have e2 : V * repu n n = ∑ t ∈ Finset.range n, V * 2 ^ (n * t) := by
    rw [repu, Finset.mul_sum]
  have hc : ∀ t < n, ((if A.testBit (n * t + k) then 1 else 0) * (2 ^ n - 1)) < 2 ^ n := by
    intro t _
    split <;> omega
  unfold stepF2
  rw [← hV, e1, e2, Nat.testBit_and, testBit_blockSum n hc i j hj,
    testBit_blockSum n (fun _ _ => hVlt) i j hj, hV, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : i < n
  · cases hb : A.testBit (n * i + k) <;> simp [hi, hj, hb, Nat.add_comm]
  · simp [hi]

@[expose] def xsum (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | m + 1 => xsum f m ^^ f m

theorem zmod2_xsum (f : ℕ → Bool) : ∀ m,
    (if xsum f m then (1 : ZMod 2) else 0) = ∑ k ∈ Finset.range m, (if f k then 1 else 0)
  | 0 => by simp [xsum]
  | m + 1 => by
    rw [xsum, Finset.sum_range_succ, ← zmod2_xsum f m]
    cases xsum f m <;> cases f m <;> decide

theorem testBit_foldF2 {n : ℕ} (hn : 0 < n) (A B : ℕ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    ∀ m, (foldF2 n A B m).testBit (n * i + j) =
      xsum (fun k => A.testBit (n * i + k) && B.testBit (n * k + j)) m
  | 0 => by simp [foldF2, xsum]
  | m + 1 => by
    rw [foldF2, Nat.testBit_xor, testBit_foldF2 hn A B hi hj m, testBit_stepF2 hn A B m hj, xsum]
    simp [hi]

theorem pkMat_mulF2 (n A B : ℕ) : pkMat n (mulF2 n A B) = pkMat n A * pkMat n B := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext i
    exact i.elim0
  ext i j
  rw [Matrix.mul_apply]
  simp only [pkMat, Matrix.of_apply]
  rw [mulF2_eq_fold hn, testBit_foldF2 hn A B i.isLt j.isLt n, zmod2_xsum,
    ← Fin.sum_univ_eq_sum_range (fun k => if A.testBit (n * i.val + k) &&
      B.testBit (n * k + j.val) then (1 : ZMod 2) else 0) n]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases A.testBit (n * i.val + k.val) <;> cases B.testBit (n * k.val + j.val) <;> simp

theorem pkMat_oneF2 (n : ℕ) : pkMat n (oneF2 n) = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext i
    exact i.elim0
  ext i j
  simp only [pkMat, Matrix.of_apply, Matrix.one_apply]
  rw [oneF2_eq]
  have key : (repu (n + 1) n).testBit (n * i.val + j.val) = decide (i = j) := by
    rw [Bool.eq_iff_iff, testBit_repu (s := n + 1) (by omega), decide_eq_true_iff]
    constructor
    · rintro ⟨t, ht, h⟩
      have h' : n * i.val + j.val = n * t + t := by rw [h]; ring
      obtain ⟨h1, h2⟩ := pos_unique j.isLt ht h'
      exact Fin.ext (by omega)
    · rintro rfl
      exact ⟨i.val, i.isLt, by ring⟩
  rw [key]
  by_cases h : i = j <;> simp [h]

theorem lenLLK_eq (L : List (List ℕ)) : CFSG.KC.Misc.G24.shape4.lenLLK L = L.length := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    show Nat.succ (CFSG.KC.Misc.G24.shape4.lenLLK xs) = xs.length + 1
    rw [ih]

theorem getD_mem_of_lt {r : List ℕ} {j : ℕ} (hj : j < r.length) : r.getD j 0 ∈ r := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

end CFSG.KC.Misc.Spec

end
