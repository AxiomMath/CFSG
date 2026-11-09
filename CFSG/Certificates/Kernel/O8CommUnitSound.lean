module

public import CFSG.Certificates.Kernel.O8UnitSound

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem mulK_zero_right8 (a : ℕ) : mulK a 0 = 0 := by
  apply eq_of_toMatK_eq (mulK_lt _ _) (by norm_num)
  rw [toMatK_mulK]
  have h0 : toMatK 0 = 0 := by
    ext i j
    simp [toMatK, bz]
  rw [h0, Matrix.mul_zero]

theorem mulK_zero_left8 (b : ℕ) : mulK 0 b = 0 := by
  apply eq_of_toMatK_eq (mulK_lt _ _) (by norm_num)
  rw [toMatK_mulK]
  have h0 : toMatK 0 = 0 := by
    ext i j
    simp [toMatK, bz]
  rw [h0, Matrix.zero_mul]

theorem mulK_idK_comm8 (c : ℕ) : mulK c idK = mulK idK c := by
  apply eq_of_toMatK_eq (mulK_lt _ _) (mulK_lt _ _)
  rw [toMatK_mulK, toMatK_mulK, toMatK_idK, Matrix.mul_one, Matrix.one_mul]

theorem testBit_mul_spread {w : ℕ} (hw : w < 2 ^ 12) : ∀ x : ℕ,
    (∀ q, x.testBit q = true → q % 12 = 0) →
    ∀ p, (x * w).testBit p = (x.testBit (12 * (p / 12)) && w.testBit (p % 12)) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  intro hx p
  rcases Nat.eq_zero_or_pos x with rfl | hx0
  · simp
  have hb : x % 2 < 2 ^ 12 := lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
  have hy : ∀ j, (x >>> 12).testBit j = x.testBit (12 + j) := fun j => Nat.testBit_shiftRight _
  have hsplit : x = 2 ^ 12 * (x >>> 12) + x % 2 := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_two_pow_mul_add _ hb, hy]
    by_cases hj : j < 12
    · rw [if_pos hj]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp [Nat.testBit_zero]
      · have h1 : x.testBit j = false := by
          cases h : x.testBit j
          · rfl
          · have := hx j h
            omega
        have h2' : (2 : ℕ) ^ 1 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj0
        rw [pow_one] at h2'
        have h2 : (x % 2).testBit j = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) h2')
        rw [h1, h2]
    · rw [if_neg hj, show 12 + (j - 12) = j by omega]
  have hylt : x >>> 12 < x := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_self hx0 (by norm_num)
  have hyx : ∀ q, (x >>> 12).testBit q = true → q % 12 = 0 := fun q h => by
    rw [hy] at h
    have := hx _ h
    omega
  have hbw : x % 2 * w < 2 ^ 12 := by
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> omega
  have e1 : x * w = 2 ^ 12 * ((x >>> 12) * w) + x % 2 * w := by
    rw [← Nat.mul_assoc, ← Nat.add_mul, ← hsplit]
  rw [e1, Nat.testBit_two_pow_mul_add _ hbw]
  conv_rhs => rw [hsplit, Nat.testBit_two_pow_mul_add _ hb]
  by_cases hp : p < 12
  · have hq : 12 * (p / 12) = 0 := by omega
    rw [if_pos hp, hq, if_pos (by norm_num), Nat.mod_eq_of_lt hp]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
  · rw [if_neg hp, ih _ hylt hyx, if_neg (by omega),
      show 12 * ((p - 12) / 12) = 12 * (p / 12) - 12 by omega,
      show (p - 12) % 12 = p % 12 by omega]

theorem spreadU8_testBit (a l q : ℕ) (h : ((a >>> l) &&& low12).testBit q = true) : q % 12 = 0 := by
  rw [Nat.testBit_and, low12_testBit] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.2

theorem mulK_row_right (a : ℕ) {l w : ℕ} (hl : l < 12) (hw : w < 2 ^ 12) :
    mulK a (2 ^ (12 * l) * w) = ((a >>> l) &&& low12) * w := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_mul_spread hw _ (spreadU8_testBit a l) p, Nat.testBit_and, low12_testBit,
    Nat.testBit_shiftRight]
  by_cases hp : p < 144
  · have e := testBit_mulK a (2 ^ (12 * l) * w) hp
    have hb : ∀ k : ℕ, k < 12 → (2 ^ (12 * l) * w).testBit (12 * k + p % 12) =
        (decide (k = l) && w.testBit (p % 12)) := by
      intro k hk
      have h0 : (0 : ℕ) < 2 ^ (12 * l) := by positivity
      have := Nat.testBit_two_pow_mul_add w h0 (12 * k + p % 12)
      rw [Nat.add_zero] at this
      rw [this]
      by_cases hkl : k = l
      · subst hkl
        rw [if_neg (by omega), show 12 * k + p % 12 - 12 * k = p % 12 by omega]
        simp
      · by_cases hlt : k < l
        · rw [if_pos (by omega), Nat.zero_testBit]
          simp [hkl]
        · rw [if_neg (by omega), Nat.testBit_lt_two_pow (lt_of_lt_of_le hw
            (Nat.pow_le_pow_right (by norm_num) (by omega)))]
          simp [hkl]
    rw [Finset.sum_eq_single ⟨l, hl⟩ (fun k _ hk => by
        rw [hb k k.isLt]
        simp [Fin.ext_iff.not.mp hk]) (by simp),
      hb l hl, ← bz_and] at e
    rw [bz_injective e]
    have h1 : 12 * (p / 12) < 144 ∧ 12 * (p / 12) % 12 = 0 := by omega
    simp [h1, Nat.add_comm l]
  · have h1 : ¬ (12 * (p / 12) < 144) := by omega
    simp [testBit_mulK_lt _ _ p (by omega), h1]

theorem testBit_of_low12 {u : ℕ} (hu : u &&& low12 = u) {q : ℕ} (h : u.testBit q = true) :
    q < 144 ∧ q % 12 = 0 := by
  rw [← hu, Nat.testBit_and, low12_testBit] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem mulK_col_left (b : ℕ) {i u : ℕ} (hi : i < 12) (hu : u &&& low12 = u) :
    mulK (2 ^ i * u) b = u * ((b >>> (12 * i)) &&& 4095) := by
  have hw : (b >>> (12 * i)) &&& 4095 < 2 ^ 12 :=
    lt_of_le_of_lt Nat.and_le_right (by norm_num)
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_mul_spread hw _ (fun q h => (testBit_of_low12 hu h).2) p, Nat.testBit_and,
    show (4095 : ℕ) = 2 ^ 12 - 1 by norm_num, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  have hp12 : p % 12 < 12 := Nat.mod_lt _ (by norm_num)
  by_cases hp : p < 144
  · have e := testBit_mulK (2 ^ i * u) b hp
    have hb : ∀ k : ℕ, k < 12 → (2 ^ i * u).testBit (12 * (p / 12) + k) =
        (decide (k = i) && u.testBit (12 * (p / 12))) := by
      intro k hk
      have h0 : (0 : ℕ) < 2 ^ i := by positivity
      have := Nat.testBit_two_pow_mul_add u h0 (12 * (p / 12) + k)
      rw [Nat.add_zero] at this
      rw [this]
      by_cases hki : k = i
      · subst hki
        rw [if_neg (by omega), show 12 * (p / 12) + k - k = 12 * (p / 12) by omega]
        simp
      · split_ifs with hq
        · simp [hki]
        · cases h : u.testBit (12 * (p / 12) + k - i)
          · simp [hki]
          · have := (testBit_of_low12 hu h).2
            omega
    rw [Finset.sum_eq_single ⟨i, hi⟩ (fun k _ hk => by
        rw [hb k k.isLt]
        simp [Fin.ext_iff.not.mp hk]) (by simp),
      hb i hi, ← bz_and] at e
    rw [bz_injective e]
    simp [hp12, Nat.add_comm (12 * i)]
  · have h1 : u.testBit (12 * (p / 12)) = false := by
      cases h : u.testBit (12 * (p / 12))
      · rfl
      · have := (testBit_of_low12 hu h).1
        omega
    simp [testBit_mulK_lt _ _ p (by omega), h1]

@[expose] noncomputable def rowsU8 (R : List (ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun p _ ih => Nat.xor (2 ^ (12 * p.1) * p.2) ih) R

@[expose] noncomputable def colsU8 (C : List (ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun p _ ih => Nat.xor (2 ^ p.1 * p.2) ih) C

@[expose] noncomputable def grpRU8 (a : ℕ) (R : List (ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun p _ ih => Nat.xor (Nat.mul (Nat.land (Nat.shiftRight a p.1) low12) p.2) ih) R

@[expose] noncomputable def grpLU8 (b : ℕ) (C : List (ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun p _ ih => Nat.xor (Nat.mul p.2 (Nat.land (Nat.shiftRight b (Nat.mul 12 p.1)) 4095)) ih) C

theorem mulK_rowsU8 (a : ℕ) :
    ∀ R : List (ℕ × ℕ), (∀ p ∈ R, p.1 < 12 ∧ p.2 < 2 ^ 12) → mulK a (rowsU8 R) = grpRU8 a R
  | [], _ => mulK_zero_right8 a
  | p :: R, h => by
    have hp := h p List.mem_cons_self
    change mulK a (2 ^ (12 * p.1) * p.2 ^^^ rowsU8 R) =
      ((a >>> p.1) &&& low12) * p.2 ^^^ grpRU8 a R
    rw [mulK_xor_right, mulK_row_right a hp.1 hp.2,
      mulK_rowsU8 a R fun q hq => h q (List.mem_cons_of_mem _ hq)]

theorem mulK_colsU8 (b : ℕ) :
    ∀ C : List (ℕ × ℕ), (∀ p ∈ C, p.1 < 12 ∧ p.2 &&& low12 = p.2) →
      mulK (colsU8 C) b = grpLU8 b C
  | [], _ => mulK_zero_left8 b
  | p :: C, h => by
    have hp := h p List.mem_cons_self
    change mulK (2 ^ p.1 * p.2 ^^^ colsU8 C) b =
      p.2 * ((b >>> (12 * p.1)) &&& 4095) ^^^ grpLU8 b C
    rw [mulK_xor_left, mulK_col_left b hp.1 hp.2,
      mulK_colsU8 b C fun q hq => h q (List.mem_cons_of_mem _ hq)]

theorem mulK_comm_grp {r : ℕ} (R C : List (ℕ × ℕ)) (hR : ∀ p ∈ R, p.1 < 12 ∧ p.2 < 2 ^ 12)
    (hC : ∀ p ∈ C, p.1 < 12 ∧ p.2 &&& low12 = p.2) (hr : r = idK ^^^ rowsU8 R)
    (hr' : r = idK ^^^ colsU8 C) (c : ℕ) :
    (mulK c r == mulK r c) = (grpRU8 c R == grpLU8 c C) := by
  have e1 : mulK c r = mulK c idK ^^^ grpRU8 c R := by
    rw [hr, mulK_xor_right, mulK_rowsU8 c R hR]
  have e2 : mulK r c = mulK c idK ^^^ grpLU8 c C := by
    rw [hr', mulK_xor_left, mulK_colsU8 c C hC, mulK_idK_comm8]
  rw [e1, e2]
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  constructor
  · intro e
    have := congrArg (mulK c idK ^^^ ·) e
    simpa only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] using this
  · intro e
    rw [e]

end CFSG.KC.O8

end
