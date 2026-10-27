module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmU0

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

open Matrix CFSG.Open

variable {w : ℕ}

abbrev Wc (w : ℕ) (i : Fin w) : Fin (w + 2) := Fin.castAdd 2 i

abbrev Tp (w : ℕ) (t : Fin 2) : Fin (w + 2) := Fin.natAdd w t

@[expose] def rhoM (A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) : Matrix (Fin w) (Fin w) F4 :=
  Matrix.of fun i j => A (Wc w i) (Wc w j)

theorem char2_eq_of_add_eq_zero {a b : F4} (h : a + b = 0) : a = b := by
  rw [add_eq_zero_iff_eq_neg.1 h, CharTwo.neg_eq]

theorem col_eq_of_mulVec {A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4} {μ : F4}
    (hμ : A *ᵥ e0 w = μ • e0 w) (i : Fin w) :
    A (Wc w i) (Tp w 0) = A (Wc w i) (Tp w 1) := by
  have h := congrFun hμ (Wc w i)
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  rw [Fin.sum_univ_add, Fin.sum_univ_two] at h
  simp only [e0_val_zero_of_castAdd, e0_natAdd_zero, e0_natAdd_one, mul_zero, mul_one,
    Finset.sum_const_zero, zero_add, add_zero] at h
  exact char2_eq_of_add_eq_zero h

theorem row_eq_of_vecMul {B : Matrix (Fin (w + 2)) (Fin (w + 2)) F4} {μ : F4}
    (hμ : e0 w ᵥ* B = μ • e0 w) (j : Fin w) :
    B (Tp w 0) (Wc w j) = B (Tp w 1) (Wc w j) := by
  have h := congrFun hμ (Wc w j)
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  rw [Fin.sum_univ_add, Fin.sum_univ_two] at h
  simp only [e0_val_zero_of_castAdd, e0_natAdd_zero, e0_natAdd_one, mul_zero, mul_one,
    Finset.sum_const_zero, zero_add, add_zero, zero_mul, one_mul] at h
  exact char2_eq_of_add_eq_zero h

theorem rhoM_mul {A B : Matrix (Fin (w + 2)) (Fin (w + 2)) F4}
    (hA : ∀ i : Fin w, A (Wc w i) (Tp w 0) = A (Wc w i) (Tp w 1))
    (hB : ∀ j : Fin w, B (Tp w 0) (Wc w j) = B (Tp w 1) (Wc w j)) :
    rhoM (A * B) = rhoM A * rhoM B := by
  ext i j
  simp only [rhoM, Matrix.of_apply, Matrix.mul_apply]
  rw [Fin.sum_univ_add, Fin.sum_univ_two, hA i, hB j, CharTwo.add_self_eq_zero, add_zero]

theorem rhoM_one : rhoM (1 : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) = 1 := by
  ext i j
  simp [rhoM, Matrix.one_apply, Wc]

theorem rhoM_unitary {A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4} (hU : IsUnitaryMat A)
    (hB : ∀ j : Fin w, A (Tp w 0) (Wc w j) = A (Tp w 1) (Wc w j)) :
    IsUnitaryMat (rhoM A) := by
  unfold IsUnitaryMat
  ext i j
  have hfull := congrFun (congrFun hU (Wc w i)) (Wc w j)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply] at hfull
  rw [Fin.sum_univ_add, Fin.sum_univ_two, hB i, hB j, CharTwo.add_self_eq_zero, add_zero] at hfull
  simp only [Fin.castAdd_inj] at hfull
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [rhoM, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  exact hfull

@[expose] def unitSub (n : ℕ) : Subgroup (GL (Fin n) F4) where
  carrier := {B | IsUnitaryMat (B : Matrix (Fin n) (Fin n) F4)}
  mul_mem' := by
    intro A B hA hB
    change IsUnitaryMat (A : Matrix (Fin n) (Fin n) F4) at hA
    change IsUnitaryMat (B : Matrix (Fin n) (Fin n) F4) at hB
    show IsUnitaryMat ((A * B : GL (Fin n) F4) : Matrix (Fin n) (Fin n) F4)
    unfold IsUnitaryMat at *
    have key : ((B : Matrix (Fin n) (Fin n) F4).map fr)ᵀ * ((A : Matrix (Fin n) (Fin n) F4).map fr)ᵀ *
        ((A : Matrix (Fin n) (Fin n) F4) * (B : Matrix (Fin n) (Fin n) F4)) =
        ((B : Matrix (Fin n) (Fin n) F4).map fr)ᵀ *
          ((((A : Matrix (Fin n) (Fin n) F4).map fr)ᵀ * (A : Matrix (Fin n) (Fin n) F4)) *
            (B : Matrix (Fin n) (Fin n) F4)) := by
      simp only [Matrix.mul_assoc]
    simp only [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    rw [key, hA, Matrix.one_mul, hB]
  one_mem' := by
    show IsUnitaryMat ((1 : GL (Fin n) F4) : Matrix (Fin n) (Fin n) F4)
    unfold IsUnitaryMat
    simp
  inv_mem' := by
    intro A hA
    change IsUnitaryMat (A : Matrix (Fin n) (Fin n) F4) at hA
    show IsUnitaryMat ((A⁻¹ : GL (Fin n) F4) : Matrix (Fin n) (Fin n) F4)
    unfold IsUnitaryMat at *
    set a : Matrix (Fin n) (Fin n) F4 := (A : Matrix (Fin n) (Fin n) F4) with ha
    set B : Matrix (Fin n) (Fin n) F4 := ((A⁻¹ : GL (Fin n) F4) : Matrix (Fin n) (Fin n) F4)
      with hB
    have hAB : a * B = 1 := by
      rw [ha, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hBeq : B = (a.map fr)ᵀ := by
      calc B = ((a.map fr)ᵀ * a) * B := by rw [hA, Matrix.one_mul]
        _ = (a.map fr)ᵀ * (a * B) := by rw [Matrix.mul_assoc]
        _ = (a.map fr)ᵀ := by rw [hAB, Matrix.mul_one]
    have hTB : (B.map fr)ᵀ = a := by
      ext i j
      simp [hBeq, fr_fr]
    rw [hTB]
    exact hAB

theorem det_pow_three_of_unitary {B : Matrix (Fin w) (Fin w) F4} (hB : IsUnitaryMat B) :
    B.det ^ 3 = 1 := by
  have h := congrArg Matrix.det hB
  rw [Matrix.det_mul, Matrix.det_one, Matrix.det_transpose] at h
  have hfd : (B.map fr).det = fr B.det := (RingHom.map_det fr B).symm
  rw [hfd, fr_apply] at h
  rw [← h]
  ring

theorem stab_col {A : GL (Fin (w + 2)) F4} (hA : A ∈ stabSU w) (i : Fin w) :
    (A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) (Wc w i) (Tp w 0) =
      (A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) (Wc w i) (Tp w 1) := by
  rw [mem_stabSU_iff] at hA
  obtain ⟨-, -, μ, hμ⟩ := hA
  exact col_eq_of_mulVec hμ i

theorem stab_row {A : GL (Fin (w + 2)) F4} (hA : A ∈ stabSU w) (j : Fin w) :
    (A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) (Tp w 0) (Wc w j) =
      (A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) (Tp w 1) (Wc w j) := by
  rw [mem_stabSU_iff] at hA
  obtain ⟨-, hU, μ, hμ⟩ := hA
  exact row_eq_of_vecMul (row_act hU hμ) j

theorem stab_unitary {A : GL (Fin (w + 2)) F4} (hA : A ∈ stabSU w) :
    IsUnitaryMat (A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) := by
  rw [mem_stabSU_iff] at hA
  exact hA.2.1

@[expose] noncomputable def rhoGL (A : ↥(stabSU w)) : GL (Fin w) F4 :=
  Units.mk (rhoM ((A : GL (Fin (w + 2)) F4) : Matrix (Fin (w + 2)) (Fin (w + 2)) F4))
    (rhoM (((A⁻¹ : ↥(stabSU w)) : GL (Fin (w + 2)) F4) : Matrix (Fin (w + 2)) (Fin (w + 2)) F4))
    (by
      rw [← rhoM_mul (stab_col A.2) (stab_row (A⁻¹ : ↥(stabSU w)).2), ← Units.val_mul]
      rw [Subgroup.coe_inv, mul_inv_cancel, Units.val_one, rhoM_one])
    (by
      rw [← rhoM_mul (stab_col (A⁻¹ : ↥(stabSU w)).2) (stab_row A.2), ← Units.val_mul]
      rw [Subgroup.coe_inv, inv_mul_cancel, Units.val_one, rhoM_one])

theorem rhoGL_val (A : ↥(stabSU w)) :
    ((rhoGL A : GL (Fin w) F4) : Matrix (Fin w) (Fin w) F4) =
      rhoM ((A : GL (Fin (w + 2)) F4) : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) := rfl

theorem rhoGL_mul (A B : ↥(stabSU w)) : rhoGL (A * B) = rhoGL A * rhoGL B := by
  apply Units.ext
  rw [rhoGL_val, Units.val_mul, rhoGL_val, rhoGL_val, Subgroup.coe_mul, Units.val_mul]
  exact rhoM_mul (stab_col A.2) (stab_row B.2)

theorem rhoGL_mem (A : ↥(stabSU w)) : rhoGL A ∈ unitSub w := by
  show IsUnitaryMat ((rhoGL A : GL (Fin w) F4) : Matrix (Fin w) (Fin w) F4)
  rw [rhoGL_val]
  exact rhoM_unitary (stab_unitary A.2) (fun j => stab_row A.2 j)

@[expose] noncomputable def rhoHom : ↥(stabSU w) →* ↥(unitSub w) :=
  MonoidHom.mk' (fun A => ⟨rhoGL A, rhoGL_mem A⟩) (fun A B => by
    apply Subtype.ext
    exact rhoGL_mul A B)

theorem rhoHom_val (A : ↥(stabSU w)) : ((rhoHom A : ↥(unitSub w)) : GL (Fin w) F4) = rhoGL A :=
  rfl

end CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

end
