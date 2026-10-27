module

public import Certificates.Data.Kernel.C7153.Check
public import CFSG.Quasithin.Vol2.KGFactU35Inputs
public import CFSG.RankThree.PartOne.HNB.F25
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.C7153

open HNUnitaryBridge CFSG.RankThree.PartOne.HNB CFSG.KC.Ord CFSG.KC.Loop
open CFSG.Quasithin.H13.KGU35 (cConj cNeg)
open Matrix

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  revert h
  cases a <;> cases b <;> decide

theorem orB_true {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  revert h
  cases a <;> cases b <;> decide

theorem sN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem beq_of_eq {x y : ℕ} (h : x = y) : Nat.beq x y = true := by
  subst h
  exact Nat.beq_refl x

theorem beq_false_of_ne {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := by
  cases hb : Nat.beq x y
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem allN_true {n : ℕ} {f : ℕ → Bool} (h : allN n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    obtain ⟨h1, h2⟩ := andB_true (a := f n) (b := allN n f) h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih h2 i hi
    · exact h1

theorem fA_eq : fA = fadd := rfl

theorem fC_eq : fC = cConj := rfl

theorem fN_eq : fN = cNeg := rfl

theorem lt25 (p q : ℕ) : p % 5 + 5 * (q % 5) < 25 := by omega

theorem fA_lt (x y : ℕ) : fA x y < 25 := by
  rw [fA_eq]
  unfold fadd
  exact lt25 _ _

theorem fC_lt (x : ℕ) : fC x < 25 := by
  rw [fC_eq]
  unfold cConj
  omega

theorem fN_lt (x : ℕ) : fN x < 25 := by
  rw [fN_eq]
  unfold cNeg
  exact lt25 _ _

theorem dec_fA (x y : ℕ) : dec (fA x y) = dec x + dec y := dec_fadd x y

theorem dec_fM (x y : ℕ) : dec (fM x y) = dec x * dec y := dec_fmul x y

theorem dec_fN (x : ℕ) : dec (fN x) = -dec x := by
  have key : ∀ x < 25, dec (cNeg x) = -dec x := by decide +kernel
  have hx : cNeg x = cNeg (x % 25) := by
    have h1 : x % 5 = x % 25 % 5 := by omega
    have h2 : x / 5 % 5 = x % 25 / 5 % 5 := by omega
    unfold cNeg
    rw [← h1, ← h2]
  rw [fN_eq, hx, dec_mod x]
  exact key _ (Nat.mod_lt _ (by norm_num))

theorem dec_fC (x : ℕ) : dec (fC x) = dec x ^ 5 := by
  have key : ∀ x < 25, dec (cConj x) = dec x ^ 5 := by decide +kernel
  have hx : cConj x = cConj (x % 25) := by
    have h1 : x % 5 = x % 25 % 5 := by omega
    have h2 : x / 5 % 5 = x % 25 / 5 % 5 := by omega
    unfold cConj
    rw [← h1, ← h2]
  rw [fC_eq, hx, dec_mod x]
  exact key _ (Nat.mod_lt _ (by norm_num))

theorem exists_code25 : ∀ x : F25, ∃ n < 25, dec n = x := by decide +kernel

theorem ent_eq (M s : ℕ) : ent M s = M / 2 ^ s % 32 := by
  change (M >>> s) &&& (2 ^ 5 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem ent_lor (a b s : ℕ) : ent (Nat.lor a b) s = Nat.lor (ent a s) (ent b s) := by
  change ((a ||| b) >>> s) &&& 31 = ((a >>> s) &&& 31) ||| ((b >>> s) &&& 31)
  rw [Nat.shiftRight_or_distrib, Nat.and_or_distrib_right]

theorem ent_shl_self {x : ℕ} (s : ℕ) (hx : x < 32) : ent (Nat.shiftLeft x s) s = x := by
  rw [ent_eq]
  change x <<< s / 2 ^ s % 32 = x
  rw [Nat.shiftLeft_eq, Nat.mul_div_cancel _ (Nat.two_pow_pos s), Nat.mod_eq_of_lt hx]

theorem ent_shl_hi (x : ℕ) {s t : ℕ} (h : s + 5 ≤ t) : ent (Nat.shiftLeft x t) s = 0 := by
  rw [ent_eq]
  change x <<< t / 2 ^ s % 32 = 0
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : x * 2 ^ (s + 5 + d) = 2 ^ s * (32 * (x * 2 ^ d)) := by
    rw [pow_add, pow_add]
    ring
  rw [Nat.shiftLeft_eq, h1, Nat.mul_div_cancel_left _ (Nat.two_pow_pos s), Nat.mul_mod_right]

theorem ent_shl_lo {x : ℕ} {s t : ℕ} (hx : x < 32) (h : t + 5 ≤ s) :
    ent (Nat.shiftLeft x t) s = 0 := by
  rw [ent_eq]
  change x <<< t / 2 ^ s % 32 = 0
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : 2 ^ (t + 5 + d) = 2 ^ t * (32 * 2 ^ d) := by
    rw [pow_add, pow_add]
    ring
  have h2 : x < 32 * 2 ^ d := lt_of_lt_of_le hx (Nat.le_mul_of_pos_right 32 (Nat.two_pow_pos d))
  rw [Nat.shiftLeft_eq, h1, mul_comm x, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos t),
    Nat.div_eq_of_lt h2, Nat.zero_mod]

theorem ent_lo_self {x : ℕ} (hx : x < 32) : ent x 0 = x := by
  rw [ent_eq, pow_zero, Nat.div_one, Nat.mod_eq_of_lt hx]

theorem ent_lo_hi {x s : ℕ} (hx : x < 32) (h : 5 ≤ s) : ent x s = 0 := by
  have h2 : (32 : ℕ) ≤ 2 ^ s := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)
  rw [ent_eq, Nat.div_eq_of_lt (lt_of_lt_of_le hx h2), Nat.zero_mod]

theorem lor_zero' (x : ℕ) : Nat.lor x 0 = x := Nat.or_zero x

theorem zero_lor' (x : ℕ) : Nat.lor 0 x = x := Nat.zero_or x

theorem ent_pk9 {x0 x1 x2 x3 x4 x5 x6 x7 x8 : ℕ} (h0 : x0 < 32) (h1 : x1 < 32) (h2 : x2 < 32)
    (h3 : x3 < 32) (h4 : x4 < 32) (h5 : x5 < 32) (h6 : x6 < 32) (h7 : x7 < 32) (h8 : x8 < 32) :
    ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 0 = x0 ∧ ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 5 = x1 ∧
      ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 10 = x2 ∧
      ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 15 = x3 ∧
      ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 20 = x4 ∧
      ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 25 = x5 ∧
      ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 30 = x6 ∧
      ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 35 = x7 ∧
      ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 40 = x8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega) only [pk9, ent_lor, ent_shl_self, ent_shl_hi, ent_shl_lo, ent_lo_self,
      ent_lo_hi, lor_zero', zero_lor']

@[expose] noncomputable def decP (M : ℕ) : Matrix (Fin 3) (Fin 3) F25 :=
  !![dec (ent M 0), dec (ent M 5), dec (ent M 10); dec (ent M 15), dec (ent M 20), dec (ent M 25);
    dec (ent M 30), dec (ent M 35), dec (ent M 40)]

theorem decP_pk9 {x0 x1 x2 x3 x4 x5 x6 x7 x8 : ℕ} (h0 : x0 < 32) (h1 : x1 < 32) (h2 : x2 < 32)
    (h3 : x3 < 32) (h4 : x4 < 32) (h5 : x5 < 32) (h6 : x6 < 32) (h7 : x7 < 32) (h8 : x8 < 32) :
    decP (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) =
      !![dec x0, dec x1, dec x2; dec x3, dec x4, dec x5; dec x6, dec x7, dec x8] := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := ent_pk9 h0 h1 h2 h3 h4 h5 h6 h7 h8
  rw [decP, e0, e1, e2, e3, e4, e5, e6, e7, e8]

theorem lt32 {x : ℕ} (h : x < 25) : x < 32 := by omega

theorem mulM_eq (A B : ℕ) : mulM A B = mul9 (ent A 0) (ent A 5) (ent A 10) (ent A 15) (ent A 20)
    (ent A 25) (ent A 30) (ent A 35) (ent A 40) (ent B 0) (ent B 5) (ent B 10) (ent B 15)
    (ent B 20) (ent B 25) (ent B 30) (ent B 35) (ent B 40) := by
  unfold mulM
  rw [sN_eq, sN_eq]

theorem decP_mulM (A B : ℕ) : decP (mulM A B) = decP A * decP B := by
  rw [mulM_eq, mul9, decP_pk9 (lt32 (fA_lt _ _)) (lt32 (fA_lt _ _)) (lt32 (fA_lt _ _))
    (lt32 (fA_lt _ _)) (lt32 (fA_lt _ _)) (lt32 (fA_lt _ _)) (lt32 (fA_lt _ _))
    (lt32 (fA_lt _ _)) (lt32 (fA_lt _ _))]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [decP, Matrix.mul_apply, Fin.sum_univ_three, dec_fA, dec_fM]

theorem decP_cT (A : ℕ) : decP (cT A) = ((decP A).map (· ^ 5))ᵀ := by
  unfold cT
  rw [sN_eq, decP_pk9 (lt32 (fC_lt _)) (lt32 (fC_lt _)) (lt32 (fC_lt _)) (lt32 (fC_lt _))
    (lt32 (fC_lt _)) (lt32 (fC_lt _)) (lt32 (fC_lt _)) (lt32 (fC_lt _)) (lt32 (fC_lt _))]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [decP, dec_fC]

theorem dec_det3 (A : ℕ) : dec (det3 A) = (decP A).det := by
  unfold det3
  rw [sN_eq, Matrix.det_fin_three]
  simp only [det9, dec_fA, dec_fM, dec_fN, decP, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  ring

theorem decP_idM : decP idM = 1 := by
  rw [idM, decP_pk9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dec_zero, dec_one, Matrix.one_apply]

theorem pow5_eq (A : ℕ) : pow5 A = mulM (mulM (mulM A A) (mulM A A)) A := by
  unfold pow5
  rw [sN_eq, sN_eq]

theorem decP_pow5 (A : ℕ) : decP (pow5 A) = decP A ^ 5 := by
  rw [pow5_eq, decP_mulM, decP_mulM, decP_mulM]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem pk9_eq_of_decP {x0 x1 x2 x3 x4 x5 x6 x7 x8 y0 y1 y2 y3 y4 y5 y6 y7 y8 : ℕ}
    (hx0 : x0 < 25) (hx1 : x1 < 25) (hx2 : x2 < 25) (hx3 : x3 < 25) (hx4 : x4 < 25)
    (hx5 : x5 < 25) (hx6 : x6 < 25) (hx7 : x7 < 25) (hx8 : x8 < 25)
    (hy0 : y0 < 25) (hy1 : y1 < 25) (hy2 : y2 < 25) (hy3 : y3 < 25) (hy4 : y4 < 25)
    (hy5 : y5 < 25) (hy6 : y6 < 25) (hy7 : y7 < 25) (hy8 : y8 < 25)
    (h : decP (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) = decP (pk9 y0 y1 y2 y3 y4 y5 y6 y7 y8)) :
    pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8 = pk9 y0 y1 y2 y3 y4 y5 y6 y7 y8 := by
  rw [decP_pk9 (lt32 hx0) (lt32 hx1) (lt32 hx2) (lt32 hx3) (lt32 hx4) (lt32 hx5) (lt32 hx6)
    (lt32 hx7) (lt32 hx8), decP_pk9 (lt32 hy0) (lt32 hy1) (lt32 hy2) (lt32 hy3) (lt32 hy4)
    (lt32 hy5) (lt32 hy6) (lt32 hy7) (lt32 hy8)] at h
  have e : ∀ i j, (!![dec x0, dec x1, dec x2; dec x3, dec x4, dec x5; dec x6, dec x7, dec x8] :
      Matrix (Fin 3) (Fin 3) F25) i j =
      (!![dec y0, dec y1, dec y2; dec y3, dec y4, dec y5; dec y6, dec y7, dec y8] :
        Matrix (Fin 3) (Fin 3) F25) i j := fun i j => by rw [h]
  have q0 := dec_injOn _ hx0 _ hy0 (by simpa using e 0 0)
  have q1 := dec_injOn _ hx1 _ hy1 (by simpa using e 0 1)
  have q2 := dec_injOn _ hx2 _ hy2 (by simpa using e 0 2)
  have q3 := dec_injOn _ hx3 _ hy3 (by simpa using e 1 0)
  have q4 := dec_injOn _ hx4 _ hy4 (by simpa using e 1 1)
  have q5 := dec_injOn _ hx5 _ hy5 (by simpa using e 1 2)
  have q6 := dec_injOn _ hx6 _ hy6 (by simpa using e 2 0)
  have q7 := dec_injOn _ hx7 _ hy7 (by simpa using e 2 1)
  have q8 := dec_injOn _ hx8 _ hy8 (by simpa using e 2 2)
  rw [q0, q1, q2, q3, q4, q5, q6, q7, q8]

theorem mulM_eq_idM {A B : ℕ} (h : decP (mulM A B) = 1) : mulM A B = idM := by
  have h' : decP (mulM A B) = decP idM := by rw [h, decP_idM]
  rw [mulM_eq, mul9] at h' ⊢
  unfold idM at h' ⊢
  exact pk9_eq_of_decP (fA_lt _ _) (fA_lt _ _) (fA_lt _ _) (fA_lt _ _) (fA_lt _ _) (fA_lt _ _)
    (fA_lt _ _) (fA_lt _ _) (fA_lt _ _) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h'

theorem decP_yOf {a c : ℕ} (ha : a < 25) (hc : c < 25) :
    decP (yOf (25 * a + c)) = !![dec a, -(dec c ^ 5), 0; dec c, dec a ^ 5, 0; 0, 0, 1] := by
  have h1 : Nat.div (25 * a + c) 25 = a := by
    have : (25 * a + c) / 25 = a := by omega
    exact this
  have h2 : Nat.mod (25 * a + c) 25 = c := by
    have : (25 * a + c) % 25 = c := by omega
    exact this
  rw [yOf, h1, h2, decP_pk9 (lt32 ha) (lt32 (fN_lt _)) (by norm_num) (lt32 hc) (lt32 (fC_lt _))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num), dec_fN, dec_fC, dec_fC, dec_zero,
    dec_one]

theorem memK_sound {W : List ℕ} {k : ℕ} (h : memK W k = true) :
    ∃ r ∈ W, Nat.land r 1023 = k := by
  induction W with
  | nil => exact absurd h Bool.false_ne_true
  | cons r W ih =>
    change orB (Nat.beq (Nat.land r 1023) k) (memK W k) = true at h
    rcases orB_true h with h | h
    · exact ⟨r, by simp, Nat.eq_of_beq_eq_true h⟩
    · obtain ⟨s, hs, e⟩ := ih h
      exact ⟨s, by simp [hs], e⟩

theorem witsG_sound {W : List ℕ} (h : witsG W = true) : ∀ r ∈ W, witG r = true := by
  induction W with
  | nil => intro r hr; simp at hr
  | cons s W ih =>
    obtain ⟨h1, h2⟩ := andB_true (a := witG s) (b := witsG W) h
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h1
    · exact ih h2 r hr

theorem walkAC_sound {W : List ℕ} (hW : walkAC W = true) {a c : ℕ} (ha : a < 25) (hc : c < 25)
    (hn : Nat.beq (fA (fM a (fC a)) (fM c (fC c))) 1 = true)
    (hp : pow5 (yOf (25 * a + c)) = idM) (hne : yOf (25 * a + c) ≠ idM) :
    ∃ r ∈ W, Nat.land r 1023 = 25 * a + c := by
  have h : caseAC W a c = true := allN_true (allN_true hW a ha) c hc
  change orB (notB (Nat.beq (fA (fM a (fC a)) (fM c (fC c))) 1))
    (letB (yOf (25 * a + c)) fun y =>
      orB (notB (andB (Nat.beq (pow5 y) idM) (notB (Nat.beq y idM))))
        (memK W (25 * a + c))) = true at h
  rcases orB_true h with h | h
  · rw [hn] at h
    exact absurd h (by decide)
  · rw [letB_eq] at h
    rcases orB_true h with h | h
    · rw [beq_of_eq hp, beq_false_of_ne hne] at h
      exact absurd h (by decide)
    · exact memK_sound h

theorem suK_sound {A : ℕ} (h : suK A = true) :
    (decP A).det = 1 ∧ ((decP A).map (· ^ 5))ᵀ * decP A = 1 := by
  obtain ⟨h1, h2⟩ := andB_true h
  refine ⟨?_, ?_⟩
  · rw [← dec_det3, Nat.eq_of_beq_eq_true h2, dec_one]
  · rw [← decP_cT, ← decP_mulM, Nat.eq_of_beq_eq_true h1, decP_idM]

theorem witAB_sound {y A B : ℕ} (h : witAB y A B = true) :
    (decP A).det = 1 ∧ ((decP A).map (· ^ 5))ᵀ * decP A = 1 ∧ (decP B).det = 1 ∧
      ((decP B).map (· ^ 5))ᵀ * decP B = 1 ∧ decP A * decP B = decP y * decP B * decP A ∧
      decP A * decP y = decP y * decP A ∧ decP B * decP y = decP y * decP B ∧
      decP A ^ 5 = 1 ∧ decP B ^ 5 = 1 := by
  obtain ⟨hA, h⟩ := andB_true h
  obtain ⟨hB, h⟩ := andB_true h
  obtain ⟨hAB, h⟩ := andB_true h
  obtain ⟨hAy, h⟩ := andB_true h
  obtain ⟨hBy, h⟩ := andB_true h
  obtain ⟨hA5, hB5⟩ := andB_true h
  obtain ⟨hA1, hA2⟩ := suK_sound hA
  obtain ⟨hB1, hB2⟩ := suK_sound hB
  refine ⟨hA1, hA2, hB1, hB2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← decP_mulM, ← decP_mulM, ← decP_mulM, Nat.eq_of_beq_eq_true hAB]
  · rw [← decP_mulM, ← decP_mulM, Nat.eq_of_beq_eq_true hAy]
  · rw [← decP_mulM, ← decP_mulM, Nat.eq_of_beq_eq_true hBy]
  · rw [← decP_pow5, Nat.eq_of_beq_eq_true hA5, decP_idM]
  · rw [← decP_pow5, Nat.eq_of_beq_eq_true hB5, decP_idM]

theorem block_of_mem {M : Matrix (Fin 3) (Fin 3) F25} (hdet : M.det = 1)
    (hu : (M.map (· ^ 5))ᵀ * M = 1)
    (ht : M * diagonal ![-1, -1, 1] = diagonal ![-1, -1, 1] * M) (h5 : M ^ 5 = 1) :
    ∃ a < 25, ∃ c < 25, decP (yOf (25 * a + c)) = M ∧
      dec a * dec a ^ 5 + dec c * dec c ^ 5 = 1 := by
  have hD : ∀ i j : Fin 3,
      M i j * ![(-1 : F25), -1, 1] j = ![(-1 : F25), -1, 1] i * M i j := by
    intro i j
    have := congrFun (congrFun ht i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  have k1 : ∀ m : F25, m * 1 = -1 * m → m = 0 := by decide +kernel
  have k2 : ∀ m : F25, m * -1 = 1 * m → m = 0 := by decide +kernel
  have h02 : M 0 2 = 0 := k1 _ (hD 0 2)
  have h12 : M 1 2 = 0 := k1 _ (hD 1 2)
  have h20 : M 2 0 = 0 := k2 _ (hD 2 0)
  have h21 : M 2 1 = 0 := k2 _ (hD 2 1)
  have hpow : ∀ n : ℕ, (M ^ n) 2 0 = 0 ∧ (M ^ n) 2 1 = 0 ∧ (M ^ n) 2 2 = M 2 2 ^ n := by
    intro n
    induction n with
    | zero => simp [Matrix.one_apply]
    | succ n ih =>
      obtain ⟨i0, i1, i2⟩ := ih
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, i0, i1, i2, h20, h21]
  have he5 : M 2 2 ^ 5 = 1 := by
    rw [← (hpow 5).2.2, h5]
    rfl
  have hu22 := congrFun (congrFun hu 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, h02, h12] at hu22
  have he : M 2 2 = 1 := by
    rw [he5, one_mul] at hu22
    exact hu22
  have hu00 := congrFun (congrFun hu 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, h20] at hu00
  have hT : (M.map (· ^ 5))ᵀ = M.adjugate := by
    rw [← Matrix.inv_eq_left_inv hu, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  have e00 := congrFun (congrFun hT 0) 0
  have e01 := congrFun (congrFun hT 0) 1
  simp [Matrix.adjugate_fin_three, he, h12, h21, h02] at e00 e01
  obtain ⟨a, ha, hda⟩ := exists_code25 (M 0 0)
  obtain ⟨c, hc, hdc⟩ := exists_code25 (M 1 0)
  refine ⟨a, ha, c, hc, ?_, ?_⟩
  · rw [decP_yOf ha hc, hda, hdc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h02, h12, h20, h21, he]
    · linear_combination -e01
    · linear_combination e00
  · rw [hda, hdc]
    linear_combination hu00

theorem c7153K_sound {W : List ℕ} (hW : c7153K W = true) {M : Matrix (Fin 3) (Fin 3) F25}
    (hdet : M.det = 1) (hu : (M.map (· ^ 5))ᵀ * M = 1)
    (ht : M * diagonal ![-1, -1, 1] = diagonal ![-1, -1, 1] * M) (h5 : M ^ 5 = 1) (h1 : M ≠ 1) :
    ∃ A B : Matrix (Fin 3) (Fin 3) F25, A.det = 1 ∧ (A.map (· ^ 5))ᵀ * A = 1 ∧ B.det = 1 ∧
      (B.map (· ^ 5))ᵀ * B = 1 ∧ A * B = M * B * A ∧ A * M = M * A ∧ B * M = M * B ∧
      A ^ 5 = 1 ∧ B ^ 5 = 1 := by
  obtain ⟨hwalk, hwits⟩ := andB_true hW
  obtain ⟨a, ha, c, hc, hy, hn⟩ := block_of_mem hdet hu ht h5
  have hn' : Nat.beq (fA (fM a (fC a)) (fM c (fC c))) 1 = true := by
    apply beq_of_eq
    apply dec_injOn _ (fA_lt _ _) _ (by norm_num)
    rw [dec_fA, dec_fM, dec_fM, dec_fC, dec_fC, hn, dec_one]
  have hp : pow5 (yOf (25 * a + c)) = idM := by
    rw [pow5_eq]
    apply mulM_eq_idM
    rw [← pow5_eq, decP_pow5, hy, h5]
  have hne : yOf (25 * a + c) ≠ idM := by
    intro h
    apply h1
    rw [← hy, h, decP_idM]
  obtain ⟨r, hr, hk⟩ := walkAC_sound hwalk ha hc hn' hp hne
  have hg := witsG_sound hwits r hr
  unfold witG at hg
  rw [letB_eq, letB_eq, letB_eq] at hg
  obtain ⟨-, hg⟩ := andB_true hg
  obtain ⟨-, hg⟩ := andB_true hg
  obtain ⟨-, hg⟩ := andB_true hg
  obtain ⟨-, hg⟩ := andB_true hg
  rw [letB_eq, hk] at hg
  obtain ⟨hA1, hA2, hB1, hB2, hAB, hAy, hBy, hA5, hB5⟩ := witAB_sound hg
  rw [hy] at hAB hAy hBy
  exact ⟨_, _, hA1, hA2, hB1, hB2, hAB, hAy, hBy, hA5, hB5⟩

section Gens

variable {G : Type*} [Group G]

theorem pow_mul_of_comm {x z w : G} (hw : z * x = x * z * w) (cz : Commute w z) (m : ℕ) :
    z ^ m * x = x * z ^ m * w ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc z ^ (m + 1) * x = z * (z ^ m * x) := by rw [pow_succ', mul_assoc]
      _ = z * x * z ^ m * w ^ m := by rw [ih]; simp only [mul_assoc]
      _ = x * z * (w * z ^ m) * w ^ m := by rw [hw]; simp only [mul_assoc]
      _ = x * z * (z ^ m * w) * w ^ m := by rw [(cz.pow_right m).eq]
      _ = x * z ^ (m + 1) * w ^ (m + 1) := by rw [pow_succ', pow_succ']; simp only [mul_assoc]

theorem mul_pow_of_comm {x z w : G} (hw : z * x = x * z * w) (cx : Commute w x) (m : ℕ) :
    z * x ^ m = x ^ m * z * w ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc z * x ^ (m + 1) = z * x ^ m * x := by rw [pow_succ, mul_assoc]
      _ = x ^ m * z * (w ^ m * x) := by rw [ih]; simp only [mul_assoc]
      _ = x ^ m * (z * x) * w ^ m := by rw [(cx.pow_left m).eq]; simp only [mul_assoc]
      _ = x ^ (m + 1) * z * w ^ (m + 1) := by
        rw [hw, pow_succ, pow_succ']
        simp only [mul_assoc]

theorem mul_pow_choose {x z w : G} (hw : z * x = x * z * w) (cx : Commute w x)
    (cz : Commute w z) (n : ℕ) : (x * z) ^ n = x ^ n * z ^ n * w ^ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (x * z) ^ (n + 1) = x ^ n * z ^ n * w ^ n.choose 2 * (x * z) := by rw [pow_succ, ih]
      _ = x ^ n * z ^ n * (w ^ n.choose 2 * x) * z := by simp only [mul_assoc]
      _ = x ^ n * z ^ n * (x * w ^ n.choose 2) * z := by rw [(cx.pow_left _).eq]
      _ = x ^ n * (z ^ n * x) * (w ^ n.choose 2 * z) := by simp only [mul_assoc]
      _ = x ^ n * (x * z ^ n * w ^ n) * (z * w ^ n.choose 2) := by
        rw [pow_mul_of_comm hw cz n, (cz.pow_left _).eq]
      _ = x ^ n * x * (z ^ n * (w ^ n * z)) * w ^ n.choose 2 := by simp only [mul_assoc]
      _ = x ^ n * x * (z ^ n * (z * w ^ n)) * w ^ n.choose 2 := by rw [(cz.pow_left n).eq]
      _ = x ^ (n + 1) * z ^ (n + 1) * w ^ (n + 1).choose 2 := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right, pow_succ x, pow_succ z, pow_add w]
        simp only [mul_assoc]

theorem star5_of_gens {y a b : G} (hab : a * b = y * b * a) (hay : a * y = y * a)
    (hby : b * y = y * b) (ha5 : a ^ 5 = 1) (hb5 : b ^ 5 = 1) (hy5 : y ^ 5 = 1) :
    ∃ a b : G, y = a * b * a⁻¹ * b⁻¹ ∧
      ∀ g ∈ Subgroup.closure ({a, b} : Set G), g ^ 5 = 1 ∧ g * y = y * g := by
  have ca : Commute a y := hay
  have cb : Commute b y := hby
  have hy5' : y * y ^ 4 = 1 := by
    rw [← pow_succ']
    exact hy5
  have hba : b * a = a * b * y ^ 4 :=
    calc b * a = b * a * (y * y ^ 4) := by rw [hy5', mul_one]
      _ = y * (b * a) * y ^ 4 := by rw [← mul_assoc, (cb.mul_left ca).eq]
      _ = a * b * y ^ 4 := by rw [hab]; simp only [mul_assoc]
  have hbJ : ∀ J : ℕ, b ^ J * a = a * b ^ J * (y ^ 4) ^ J :=
    pow_mul_of_comm hba (cb.pow_right 4).symm
  have hIJ : ∀ I J : ℕ, b ^ J * a ^ I = a ^ I * b ^ J * y ^ (4 * (J * I)) := by
    intro I J
    rw [mul_pow_of_comm (hbJ J) ((ca.pow_right 4).pow_right J).symm I, ← pow_mul, ← pow_mul]
  have hy5k : ∀ m : ℕ, (y ^ m) ^ 5 = 1 := fun m => by
    rw [← pow_mul, mul_comm, pow_mul, hy5, one_pow]
  set P : G → Prop := fun g => ∃ i j k : ℕ, g = a ^ i * b ^ j * y ^ k with hP
  have hstep : ∀ x ∈ ({a, b} : Set G), ∀ g, P g → P (x * g) := by
    rintro x hx g ⟨i, j, k, rfl⟩
    rcases hx with hx | hx
    · rw [hx]
      exact ⟨i + 1, j, k, by rw [pow_succ']; simp only [mul_assoc]⟩
    · have hx' : x = b := hx
      rw [hx']
      have e := hIJ i 1
      simp only [pow_one, one_mul] at e
      refine ⟨i, j + 1, 4 * i + k, ?_⟩
      calc b * (a ^ i * b ^ j * y ^ k) = b * a ^ i * b ^ j * y ^ k := by simp only [mul_assoc]
        _ = a ^ i * b * (y ^ (4 * i) * b ^ j) * y ^ k := by rw [e]; simp only [mul_assoc]
        _ = a ^ i * b * (b ^ j * y ^ (4 * i)) * y ^ k := by
          rw [(cb.pow_pow j (4 * i)).symm.eq]
        _ = a ^ i * b ^ (j + 1) * y ^ (4 * i + k) := by
          rw [pow_succ', pow_add]
          simp only [mul_assoc]
  have hpow : ∀ x ∈ ({a, b} : Set G), ∀ n : ℕ, ∀ g, P g → P (x ^ n * g) := by
    intro x hx n
    induction n with
    | zero => intro g hg; simpa using hg
    | succ n ih =>
      intro g hg
      rw [pow_succ', mul_assoc]
      exact hstep x hx _ (ih g hg)
  have hclos : ∀ g ∈ Subgroup.closure ({a, b} : Set G), P g := by
    intro g hg
    induction hg using Subgroup.closure_induction_left with
    | one => exact ⟨0, 0, 0, by simp⟩
    | mul_left x hx g _ ih => exact hstep x hx g ih
    | inv_mul_cancel x hx g _ ih =>
      have h5 : x ^ 5 = 1 := by
        rcases hx with rfl | rfl
        · exact ha5
        · exact hb5
      have hinv : x⁻¹ = x ^ 4 := by
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_succ']
        exact h5
      rw [hinv]
      exact hpow x hx 4 g ih
  refine ⟨a, b, ?_, fun g hg => ?_⟩
  · rw [hab]
    group
  · obtain ⟨i, j, k, rfl⟩ := hclos g hg
    refine ⟨?_, ?_⟩
    · have cxz : Commute (a ^ i * b ^ j) (y ^ k) := (ca.pow_pow i k).mul_left (cb.pow_pow j k)
      have hw : (y ^ (4 * (j * i))) ^ (5 : ℕ).choose 2 = 1 := by
        have hc : (5 : ℕ).choose 2 = 5 * 2 := by decide
        rw [hc, pow_mul, hy5k, one_pow]
      rw [cxz.mul_pow, mul_pow_choose (hIJ i j) (ca.pow_pow i _).symm (cb.pow_pow j _).symm, hw,
        hy5k, ← pow_mul, mul_comm i, pow_mul, ha5, ← pow_mul, mul_comm j, pow_mul, hb5]
      simp
    · exact (((ca.pow_left i).mul_left (cb.pow_left j)).mul_left
        ((Commute.refl y).pow_left k)).eq

end Gens

end CFSG.KC.C7153

end
