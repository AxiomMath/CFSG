module

public import Certificates.Data.Kernel.G28.R2
public import Certificates.Data.Kernel.Misc.PermClos
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Bin
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.G28R

open CFSG.RankThree.PartTwo.Sec4.Item434G28 CFSG.Quasithin CFSG.KC.Misc.Clos CFSG.KC.LQT

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by
  cases y <;> rfl

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem allN_iff (m : ℕ) (f : ℕ → Bool) : allN m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => simp [allN]
  | succ m ih =>
    change (f m && allN m f) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h m (Nat.lt_succ_self m), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem anyN_iff (m : ℕ) (f : ℕ → Bool) : anyN m f = true ↔ ∃ i < m, f i = true := by
  induction m with
  | zero => simp [anyN]
  | succ m ih =>
    change (f m || anyN m f) = true ↔ _
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨m, Nat.lt_succ_self m, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem tb_land (a b n : ℕ) : (Nat.land a b).testBit n = (a.testBit n && b.testBit n) :=
  Nat.testBit_and a b n

theorem tb_lor (a b n : ℕ) : (Nat.lor a b).testBit n = (a.testBit n || b.testBit n) :=
  Nat.testBit_or a b n

theorem tb_xor (a b n : ℕ) : (Nat.xor a b).testBit n = (a.testBit n ^^ b.testBit n) :=
  Nat.testBit_xor a b n

theorem tb_shl (a k n : ℕ) :
    (Nat.shiftLeft a k).testBit n = (decide (n ≥ k) && a.testBit (n - k)) :=
  Nat.testBit_shiftLeft a

theorem tb_shr (a k n : ℕ) : (Nat.shiftRight a k).testBit n = a.testBit (k + n) :=
  Nat.testBit_shiftRight a

theorem colM_bit (m : ℕ) : colM.testBit m = decide (m < 36 ∧ m % 6 = 0) := by
  by_cases hm : m < 36
  · have h : ∀ m : Fin 36, colM.testBit m = decide (m.val < 36 ∧ m.val % 6 = 0) := by
      decide +kernel
    exact h ⟨m, hm⟩
  · have hlt : colM < 2 ^ m :=
      lt_of_lt_of_le (by norm_num [colM]) (Nat.pow_le_pow_right (by norm_num) (by omega) :
        2 ^ 36 ≤ 2 ^ m)
    rw [Nat.testBit_eq_false_of_lt hlt]
    simp [hm]

theorem bit63 (m : ℕ) : (63 : ℕ).testBit m = decide (m < 6) := by
  have h := Nat.testBit_two_pow_sub_one 6 m
  simpa using h

theorem maskK_bit (m : ℕ) : maskK.testBit m = decide (m < 36) := by
  have h := Nat.testBit_two_pow_sub_one 36 m
  simpa [maskK] using h

theorem bz_and (x y : Bool) : bz (x && y) = bz x * bz y := by
  cases x <;> cases y <;> simp [bz]

theorem dec2_m2K (a b : ℕ) : dec2 (m2K a b) = dec2 a * dec2 b := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_six]
  simp only [dec2, Matrix.of_apply, m2K, letN_eq, trK, spK, rpK, tb_land, tb_lor, tb_xor, tb_shl,
    tb_shr, Nat.mul_eq, colM_bit, bit63, maskK_bit]
  fin_cases i <;> fin_cases j <;> simp [bz_xor, bz_and] <;> ring

theorem m2K_lt (a b : ℕ) : m2K a b < 2 ^ 36 := by
  rw [m2K, letN_eq, letN_eq]
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num [maskK])

theorem idK_lt : idK < 2 ^ 36 := id2_lt

theorem dec2_idK : dec2 idK = 1 := dec2_id2

end CFSG.KC.G28R

end
