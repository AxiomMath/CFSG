module

public import CFSG.LieType.SpecialLinear.EndNode.Blocks
public import CFSG.Quasithin.Background.SmithCurtisBasic

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.SpecialLinear

noncomputable section

section Support

variable {n : ℕ} {F : Type} [Field F]

@[expose] def rowSupportMat (a : Fin (n+1) → F) : Matrix (Fin (n+1)) (Fin (n+1)) F :=
  Matrix.of fun i j => if i = 0 then a j else 0

@[expose] def colSupportMat (a : Fin (n+1) → F) : Matrix (Fin (n+1)) (Fin (n+1)) F :=
  Matrix.of fun i j => if j = Fin.last n then a i else 0

@[simp] theorem rowSupportMat_apply (a : Fin (n+1) → F) (i j : Fin (n+1)) :
    rowSupportMat a i j = if i = 0 then a j else 0 := rfl

@[simp] theorem colSupportMat_apply (a : Fin (n+1) → F) (i j : Fin (n+1)) :
    colSupportMat a i j = if j = Fin.last n then a i else 0 := rfl

theorem rowSupportMat_isUpperTriangular {a : Fin (n+1) → F} (_ha : a 0 = 0) :
    (rowSupportMat a).IsUpperTriangular := by
  intro i j hji
  rw [rowSupportMat_apply]
  by_cases hi : i = 0
  · subst hi
    exact absurd hji (not_lt_of_ge (Fin.zero_le j))
  · simp [hi]

theorem rowSupportMat_diag {a : Fin (n+1) → F} (ha : a 0 = 0) (i : Fin (n+1)) :
    rowSupportMat a i i = 0 := by
  rw [rowSupportMat_apply]
  by_cases hi : i = 0
  · subst hi
    simp [ha]
  · simp [hi]

theorem colSupportMat_isUpperTriangular {a : Fin (n+1) → F}
    (_ha : a (Fin.last n) = 0) : (colSupportMat a).IsUpperTriangular := by
  intro i j hji
  rw [colSupportMat_apply]
  by_cases hj : j = Fin.last n
  · subst hj
    exact absurd hji (not_lt_of_ge (Fin.le_last i))
  · simp [hj]

theorem colSupportMat_diag {a : Fin (n+1) → F} (ha : a (Fin.last n) = 0)
    (i : Fin (n+1)) : colSupportMat a i i = 0 := by
  rw [colSupportMat_apply]
  by_cases hi : i = Fin.last n
  · subst hi
    simp [ha]
  · simp [hi]

theorem rowSupportMat_mul_colSupportMat {n : ℕ} (a b : Fin (n+1) → F) :
    rowSupportMat a * colSupportMat b =
      Matrix.of fun i j =>
        if i = 0 ∧ j = Fin.last n then ∑ q, a q * b q else 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.of_apply]
  by_cases hi : i = 0
  · by_cases hj : j = Fin.last n
    · simp [hi, hj]
    · simp [hi, hj]
  · simp [hi]

theorem rowSupportMat_mul_colSupportMat_apply {n : ℕ} (a b : Fin (n+1) → F)
    (i j : Fin (n+1)) :
    (rowSupportMat a * colSupportMat b) i j =
      if i = 0 ∧ j = Fin.last n then ∑ q, a q * b q else 0 := by
  rw [rowSupportMat_mul_colSupportMat, Matrix.of_apply]

@[expose] noncomputable def upperUnit {F : Type} [Field F] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) F) (htri : N.IsUpperTriangular) (hdiag : ∀ i, N i i = 0) :
    SpecialLinearGroup (Fin n) F :=
  ⟨1 + N, by
    have h : (1 + N).IsUpperTriangular := by
      intro i j hij
      have h1 : (1 : Matrix (Fin n) (Fin n) F) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij)
      have h2 : N i j = 0 := htri hij
      rw [Matrix.add_apply, h1, h2, add_zero]
    rw [Matrix.det_of_isUpperTriangular h]
    exact Finset.prod_eq_one fun i _ => by
      have h1 : (1 : Matrix (Fin n) (Fin n) F) i i = 1 := Matrix.one_apply_eq i
      have h2 : N i i = 0 := hdiag i
      rw [Matrix.add_apply, h1, h2, add_zero]⟩

@[simp] theorem coe_upperUnit {F : Type} [Field F] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) F) (htri : N.IsUpperTriangular) (hdiag : ∀ i, N i i = 0) :
    ((upperUnit N htri hdiag : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 + N := rfl

end Support

section BlockForms

variable {m : ℕ} {F : Type} [Field F]

theorem one_add_colSupportMat_eq_embedSucc {b : Fin (m+3) → F}
    (hb0 : b 0 = 0) (_hbl : b (Fin.last (m+2)) = 0) :
    (1 + colSupportMat (n := m+2) b : Matrix (Fin (m+3)) (Fin (m+3)) F) =
      embedSuccMat (m+1) F
        (1 + colSupportMat (n := m+1) (fun j : Fin (m+2) => b j.succ)) := by
  have hl0 : (Fin.last (m+2) : Fin (m+3)) ≠ 0 := by
    intro h
    rw [Fin.last_eq_zero_iff] at h
    omega
  ext i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · simp only [Matrix.add_apply, colSupportMat_apply, embedSuccMat,
        fromBlocksFirst_apply_zero_zero, Matrix.one_apply_eq, Ne.symm hl0, if_false,
        add_zero]
    · simp only [Matrix.add_apply, colSupportMat_apply, embedSuccMat,
        fromBlocksFirst_apply_zero_succ, Fin.succ_eq_last_succ, Matrix.one_apply]
      split_ifs <;> simp_all
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · simp only [Matrix.add_apply, colSupportMat_apply, embedSuccMat,
        fromBlocksFirst_apply_succ_zero, Matrix.one_apply, Fin.succ_ne_zero, Ne.symm hl0,
        if_false, add_zero, Matrix.zero_apply]
    · simp only [Matrix.add_apply, colSupportMat_apply, embedSuccMat,
        fromBlocksFirst_apply_succ_succ, Fin.succ_eq_last_succ, Matrix.one_apply,
        Fin.succ_inj]

end BlockForms

end

end CFSG.LieType.SpecialLinear
