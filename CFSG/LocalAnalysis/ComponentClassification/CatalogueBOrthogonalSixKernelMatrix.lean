module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixPfaffian

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix

private theorem elementary_skew {F : Type*} [Field F] (i j : Fin 4) :
    (Matrix.single i j (1 : F) - Matrix.single j i 1).transpose =
      -(Matrix.single i j (1 : F) - Matrix.single j i 1) := by
  rw [Matrix.transpose_sub, Matrix.transpose_single, Matrix.transpose_single]
  exact (neg_sub _ _).symm

private theorem fixed_elementary_left {F : Type*} [Field F] (g : GL (Fin 4) F)
    (h : ∀ X : Matrix (Fin 4) (Fin 4) F, X.transpose = -X →
      g.val * X * g.val.transpose = X) (i j : Fin 4) :
    g.val * (Matrix.single i j 1 - Matrix.single j i 1) =
      (Matrix.single i j 1 - Matrix.single j i 1) * g⁻¹.val.transpose := by
  have hi : g.val.transpose * g⁻¹.val.transpose = 1 := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  have hh := congrArg (fun X : Matrix (Fin 4) (Fin 4) F => X * g⁻¹.val.transpose)
    (h _ (elementary_skew i j))
  simpa only [Matrix.mul_assoc, hi, Matrix.mul_one] using hh

private theorem fixed_elementary_off_plane {F : Type*} [Field F] (g : GL (Fin 4) F)
    (h : ∀ X : Matrix (Fin 4) (Fin 4) F, X.transpose = -X →
      g.val * X * g.val.transpose = X) (i j r : Fin 4)
    (hij : i ≠ j) (hri : r ≠ i) (hrj : r ≠ j) : g.val r i = 0 := by
  have hh := congrArg (fun X : Matrix (Fin 4) (Fin 4) F => X r j)
    (fixed_elementary_left g h i j)
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply,
    Matrix.mul_single_apply_same, mul_one,
    Matrix.mul_single_apply_of_ne 1 j i r j hij.symm g.val,
    Matrix.single_mul_apply_of_ne 1 i j r j hri g⁻¹.val.transpose,
    Matrix.single_mul_apply_of_ne 1 j i r j hrj g⁻¹.val.transpose,
    sub_zero, sub_self] using hh

private theorem fixed_skew_off_diagonal {F : Type*} [Field F] (g : GL (Fin 4) F)
    (h : ∀ X : Matrix (Fin 4) (Fin 4) F, X.transpose = -X →
      g.val * X * g.val.transpose = X) (r i : Fin 4) (hri : r ≠ i) : g.val r i = 0 := by
  have hj : ∃ j : Fin 4, j ≠ i ∧ j ≠ r := by
    fin_cases i <;> fin_cases r <;> decide
  obtain ⟨j, hji, hjr⟩ := hj
  exact fixed_elementary_off_plane g h i j r hji.symm hri hjr.symm

private theorem fixed_skew_pair {F : Type*} [Field F] (g : GL (Fin 4) F)
    (h : ∀ X : Matrix (Fin 4) (Fin 4) F, X.transpose = -X →
      g.val * X * g.val.transpose = X) (i j : Fin 4) (hij : i ≠ j) :
    g.val i i * g.val j j = 1 := by
  have hh := congrArg (fun X : Matrix (Fin 4) (Fin 4) F => X i j)
    (h _ (elementary_skew i j))
  have hd : g.val = Matrix.diagonal (fun k => g.val k k) := by
    apply Matrix.ext
    intro r s
    by_cases hrs : r = s
    · subst s
      simp
    · simp [Matrix.diagonal, hrs, fixed_skew_off_diagonal g h r s hrs]
  rw [hd] at hh
  simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, hij, hij.symm] using hh

theorem fixed_skew_matrix_sign {F : Type*} [Field F] (g : GL (Fin 4) F)
    (h : ∀ X : Matrix (Fin 4) (Fin 4) F, X.transpose = -X →
      g.val * X * g.val.transpose = X) :
    g.val = 1 ∨ g.val = -(1 : Matrix (Fin 4) (Fin 4) F) := by
  have h01 := fixed_skew_pair g h 0 1 (by decide)
  have h02 := fixed_skew_pair g h 0 2 (by decide)
  have h12 := fixed_skew_pair g h 1 2 (by decide)
  have h10 : g.val 1 1 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h01
    exact zero_ne_one h01
  have h00 : g.val 0 0 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h01
    exact zero_ne_one h01
  have heq : ∀ i : Fin 4, g.val i i = g.val 0 0 := by
    intro i
    by_cases hi : i = 0
    · subst i
      rfl
    have h0i := fixed_skew_pair g h 0 i (Ne.symm hi)
    have hsame : g.val 1 1 = g.val 2 2 := mul_left_cancel₀ h00 (h01.trans h02.symm)
    have h00eq : g.val 0 0 = g.val 2 2 := by
      apply mul_right_cancel₀ h10
      calc
        g.val 0 0 * g.val 1 1 = 1 := h01
        _ = g.val 2 2 * g.val 1 1 := (mul_comm _ _).trans h12 |>.symm
    exact (mul_left_cancel₀ h00 (h0i.trans h01.symm)).trans (hsame.trans h00eq.symm)
  have hs : (g.val 0 0) ^ 2 = 1 := by simpa [pow_two, heq 1] using h01
  obtain hsign | hsign := sq_eq_one_iff.mp hs
  · left
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp [heq i, hsign]
    · simp [hij, fixed_skew_off_diagonal g h i j hij]
  · right
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp [heq i, hsign]
    · simp [hij, fixed_skew_off_diagonal g h i j hij]

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
