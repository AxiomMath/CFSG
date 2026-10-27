module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.OddStandard.AltStdSmall4.GL62

namespace Code

@[expose] def bitZ (m k : ℕ) : ZMod 2 := if m.testBit k then 1 else 0

@[expose] def vec (n : ℕ) : Fin 6 → ZMod 2 := fun i => bitZ n i

@[expose] def mat (m : ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => bitZ m (6 * j + i)

@[expose] def col (m j : ℕ) : ℕ := (m >>> (6 * j)) &&& 63

@[expose] def sel (v j c : ℕ) : ℕ := if v.testBit j then c else 0

@[expose] def act (m v : ℕ) : ℕ :=
  sel v 0 (col m 0) ^^^ sel v 1 (col m 1) ^^^ sel v 2 (col m 2) ^^^ sel v 3 (col m 3) ^^^
    sel v 4 (col m 4) ^^^ sel v 5 (col m 5)

@[expose] def pack (c₀ c₁ c₂ c₃ c₄ c₅ : ℕ) : ℕ :=
  c₀ + 64 * (c₁ + 64 * (c₂ + 64 * (c₃ + 64 * (c₄ + 64 * c₅))))

@[expose] def actCols (a₀ a₁ a₂ a₃ a₄ a₅ v : ℕ) : ℕ :=
  sel v 0 a₀ ^^^ sel v 1 a₁ ^^^ sel v 2 a₂ ^^^ sel v 3 a₃ ^^^ sel v 4 a₄ ^^^ sel v 5 a₅

@[expose] def mul (a b : ℕ) : ℕ :=
  let a₀ := col a 0
  let a₁ := col a 1
  let a₂ := col a 2
  let a₃ := col a 3
  let a₄ := col a 4
  let a₅ := col a 5
  pack (actCols a₀ a₁ a₂ a₃ a₄ a₅ (col b 0)) (actCols a₀ a₁ a₂ a₃ a₄ a₅ (col b 1))
    (actCols a₀ a₁ a₂ a₃ a₄ a₅ (col b 2)) (actCols a₀ a₁ a₂ a₃ a₄ a₅ (col b 3))
    (actCols a₀ a₁ a₂ a₃ a₄ a₅ (col b 4)) (actCols a₀ a₁ a₂ a₃ a₄ a₅ (col b 5))

theorem mul_eq (a b : ℕ) : mul a b = pack (act a (col b 0)) (act a (col b 1))
    (act a (col b 2)) (act a (col b 3)) (act a (col b 4)) (act a (col b 5)) := rfl

@[expose] def one : ℕ := 34630287489

theorem one_eq_pack : one = pack 1 2 4 8 16 32 := rfl

theorem bitZ_xor (a b k : ℕ) : bitZ (a ^^^ b) k = bitZ a k + bitZ b k := by
  unfold bitZ
  rw [Nat.testBit_xor]
  cases a.testBit k <;> cases b.testBit k <;> decide

theorem bitZ_sel (v j c k : ℕ) : bitZ (sel v j c) k = bitZ v j * bitZ c k := by
  unfold sel bitZ
  cases v.testBit j <;> simp

theorem bitZ_col (m j : ℕ) {i : ℕ} (hi : i < 6) : bitZ (col m j) i = bitZ m (6 * j + i) := by
  unfold bitZ col
  rw [Nat.testBit_and, Nat.testBit_shiftRight, show (63 : ℕ) = 2 ^ 6 - 1 by norm_num,
    Nat.testBit_two_pow_sub_one]
  simp [hi]

theorem col_lt (m j : ℕ) : col m j < 64 :=
  Nat.and_lt_two_pow _ (n := 6) (by norm_num)

theorem sel_lt (v j c : ℕ) (hc : c < 64) : sel v j c < 64 := by
  unfold sel
  split
  · exact hc
  · norm_num

theorem act_lt (m v : ℕ) : act m v < 64 := by
  have h : ∀ j, sel v j (col m j) < 2 ^ 6 := fun j => sel_lt v j _ (col_lt m j)
  unfold act
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
    (Nat.xor_lt_two_pow (h 0) (h 1)) (h 2)) (h 3)) (h 4)) (h 5)

theorem vec_act (m v : ℕ) : vec (act m v) = (mat m).mulVec (vec v) := by
  funext i
  have hi := i.isLt
  simp only [vec, act, bitZ_xor, bitZ_sel, bitZ_col m _ hi, Matrix.mulVec, dotProduct,
    Fin.sum_univ_six, mat, Matrix.of_apply]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, zero_add]
  norm_num
  ring

theorem testBit_pack_step {c r : ℕ} (hc : c < 64) (k : ℕ) :
    (c + 64 * r).testBit k = if k < 6 then c.testBit k else r.testBit (k - 6) := by
  rw [show c + 64 * r = 2 ^ 6 * r + c by ring]
  exact Nat.testBit_two_pow_mul_add r (by simpa using hc) k

theorem pack_lt {c₀ c₁ c₂ c₃ c₄ c₅ : ℕ} (h₀ : c₀ < 64) (h₁ : c₁ < 64) (h₂ : c₂ < 64)
    (h₃ : c₃ < 64) (h₄ : c₄ < 64) (h₅ : c₅ < 64) : pack c₀ c₁ c₂ c₃ c₄ c₅ < 2 ^ 36 := by
  unfold pack
  norm_num
  omega

theorem mul_lt (a b : ℕ) : mul a b < 2 ^ 36 :=
  mul_eq a b ▸ pack_lt (act_lt _ _) (act_lt _ _) (act_lt _ _) (act_lt _ _) (act_lt _ _) (act_lt _ _)

theorem one_lt : one < 2 ^ 36 := by decide

theorem testBit_step_lt {c r : ℕ} (hc : c < 64) {k : ℕ} (hk : k < 6) :
    (c + 64 * r).testBit k = c.testBit k := by
  rw [testBit_pack_step hc, ite_eq_left hk]

theorem testBit_step_ge {c r : ℕ} (hc : c < 64) (k : ℕ) :
    (c + 64 * r).testBit (k + 6) = r.testBit k := by
  rw [testBit_pack_step hc, ite_eq_right (by omega), Nat.add_sub_cancel]

theorem testBit_pack {c₀ c₁ c₂ c₃ c₄ c₅ : ℕ} (h₀ : c₀ < 64) (h₁ : c₁ < 64) (h₂ : c₂ < 64)
    (h₃ : c₃ < 64) (h₄ : c₄ < 64) (j : Fin 6) {i : ℕ} (hi : i < 6) :
    (pack c₀ c₁ c₂ c₃ c₄ c₅).testBit (6 * j + i) =
      (![c₀, c₁, c₂, c₃, c₄, c₅] j).testBit i := by
  unfold pack
  fin_cases j
  · show (c₀ + 64 * _).testBit (6 * 0 + i) = c₀.testBit i
    rw [Nat.mul_zero, Nat.zero_add, testBit_step_lt h₀ hi]
  · show (c₀ + 64 * _).testBit (6 * 1 + i) = c₁.testBit i
    rw [show 6 * 1 + i = i + 6 by omega, testBit_step_ge h₀, testBit_step_lt h₁ hi]
  · show (c₀ + 64 * _).testBit (6 * 2 + i) = c₂.testBit i
    rw [show 6 * 2 + i = i + 6 + 6 by omega, testBit_step_ge h₀, testBit_step_ge h₁,
      testBit_step_lt h₂ hi]
  · show (c₀ + 64 * _).testBit (6 * 3 + i) = c₃.testBit i
    rw [show 6 * 3 + i = i + 6 + 6 + 6 by omega, testBit_step_ge h₀, testBit_step_ge h₁,
      testBit_step_ge h₂, testBit_step_lt h₃ hi]
  · show (c₀ + 64 * _).testBit (6 * 4 + i) = c₄.testBit i
    rw [show 6 * 4 + i = i + 6 + 6 + 6 + 6 by omega, testBit_step_ge h₀, testBit_step_ge h₁,
      testBit_step_ge h₂, testBit_step_ge h₃, testBit_step_lt h₄ hi]
  · show (c₀ + 64 * _).testBit (6 * 5 + i) = c₅.testBit i
    rw [show 6 * 5 + i = i + 6 + 6 + 6 + 6 + 6 by omega, testBit_step_ge h₀, testBit_step_ge h₁,
      testBit_step_ge h₂, testBit_step_ge h₃, testBit_step_ge h₄]

theorem bitZ_mul (a b : ℕ) (i j : Fin 6) :
    bitZ (mul a b) (6 * j + i) = bitZ (act a (col b j)) i := by
  unfold bitZ
  rw [mul_eq, testBit_pack (act_lt _ _) (act_lt _ _) (act_lt _ _) (act_lt _ _) (act_lt _ _) j
    i.isLt]
  fin_cases j <;> rfl

theorem mat_mul (a b : ℕ) : mat (mul a b) = mat a * mat b := by
  ext i j
  rw [mat, Matrix.of_apply, bitZ_mul, show bitZ (act a (col b j)) i = vec (act a (col b j)) i
    from rfl, vec_act, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [vec, bitZ_col b j k.isLt]
  rfl

theorem testBit_eq_of_bitZ_eq {a b k : ℕ} (h : bitZ a k = bitZ b k) :
    a.testBit k = b.testBit k := by
  unfold bitZ at h
  cases ha : a.testBit k <;> cases hb : b.testBit k <;> simp_all

theorem eq_of_mat_eq {a b : ℕ} (ha : a < 2 ^ 36) (hb : b < 2 ^ 36) (h : mat a = mat b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 36
  · have h1 := congrFun (congrFun h ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩) ⟨k / 6, by omega⟩
    simp only [mat, Matrix.of_apply] at h1
    rw [show 6 * (k / 6) + k % 6 = k by omega] at h1
    exact testBit_eq_of_bitZ_eq h1
  · have h36 : 2 ^ 36 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem mat_one : mat one = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem mat_apply_col (m : ℕ) (i j : Fin 6) : mat m i j = bitZ (col m j) i :=
  (bitZ_col m j i.isLt).symm

theorem col_pack {c₀ c₁ c₂ c₃ c₄ c₅ : ℕ} (h₀ : c₀ < 64) (h₁ : c₁ < 64) (h₂ : c₂ < 64)
    (h₃ : c₃ < 64) (h₄ : c₄ < 64) (h₅ : c₅ < 64) (j : Fin 6) :
    col (pack c₀ c₁ c₂ c₃ c₄ c₅) j = ![c₀, c₁, c₂, c₃, c₄, c₅] j := by
  have hj : ![c₀, c₁, c₂, c₃, c₄, c₅] j < 2 ^ 6 := by
    fin_cases j <;> simpa
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · rw [← testBit_pack h₀ h₁ h₂ h₃ h₄ j hi]
    unfold col
    rw [Nat.testBit_and, Nat.testBit_shiftRight, show (63 : ℕ) = 2 ^ 6 - 1 by norm_num,
      Nat.testBit_two_pow_sub_one]
    simp [hi]
  · have h6 : 2 ^ 6 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by have := col_lt (pack c₀ c₁ c₂ c₃ c₄ c₅) j; omega),
      Nat.testBit_lt_two_pow (by omega)]

theorem mat_mul_eq_one {m m' : ℕ} (h : mul m m' = one) : mat m * mat m' = 1 := by
  rw [← mat_mul, h, mat_one]

@[expose] def decodeGL (m m' : ℕ) (h : mul m m' = one ∧ mul m' m = one) :
    GL (Fin 6) (ZMod 2) :=
  ⟨mat m, mat m', mat_mul_eq_one h.1, mat_mul_eq_one h.2⟩

@[simp] theorem coe_decodeGL (m m' : ℕ) (h : mul m m' = one ∧ mul m' m = one) :
    (decodeGL m m' h : Matrix (Fin 6) (Fin 6) (ZMod 2)) = mat m := rfl

@[simp] theorem coe_decodeGL_inv (m m' : ℕ) (h : mul m m' = one ∧ mul m' m = one) :
    (((decodeGL m m' h)⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = mat m' :=
  rfl

end Code

end CFSG.OddStandard.AltStdSmall4.GL62
