module

public import CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical

public section

namespace CFSG.GH74.Uniqueness.Bender

open Matrix CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical

section O3

variable {k : Type*} [Field k] [CharP k 2]

@[expose] def basisMat : Matrix (Fin 3) (Fin 3) k := !![1, 1, 0; 1, 1, 1; 1, 0, 1]

@[expose] def basisInv : Matrix (Fin 3) (Fin 3) k := !![1, 1, 1; 0, 1, 1; 1, 1, 0]

@[expose] def gramMat : Matrix (Fin 3) (Fin 3) k := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

@[expose] def blockOne (A : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 3) (Fin 3) k :=
  !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

theorem basisMat_mul_basisInv : basisMat * basisInv = (1 : Matrix (Fin 3) (Fin 3) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisMat, basisInv, Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

theorem basisInv_mul_basisMat : basisInv * basisMat = (1 : Matrix (Fin 3) (Fin 3) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisMat, basisInv, Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

theorem basisMat_gram : (basisMat : Matrix (Fin 3) (Fin 3) k)ᵀ * basisMat = gramMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisMat, gramMat, Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

omit [CharP k 2] in
theorem blockOne_mul (A B : Matrix (Fin 2) (Fin 2) k) :
    blockOne (A * B) = blockOne A * blockOne B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockOne, Matrix.mul_apply, Fin.sum_univ_succ]

omit [CharP k 2] in
theorem blockOne_one : blockOne (1 : Matrix (Fin 2) (Fin 2) k) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockOne]

theorem blockOne_gram (A : Matrix (Fin 2) (Fin 2) k) (hA : A.det = 1) :
    (blockOne A)ᵀ * gramMat * blockOne A = gramMat := by
  rw [Matrix.det_fin_two] at hA
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockOne, gramMat, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals first
    | linear_combination (A 1 0 * A 0 0) * h2
    | linear_combination hA + (A 0 1 * A 1 0) * h2
    | linear_combination (A 0 1 * A 1 1) * h2

theorem basisInv_gram : (basisInv : Matrix (Fin 3) (Fin 3) k)ᵀ * gramMat * basisInv = 1 := by
  rw [← basisMat_gram]
  calc (basisInv : Matrix (Fin 3) (Fin 3) k)ᵀ * (basisMatᵀ * basisMat) * basisInv
      = (basisMat * basisInv)ᵀ * (basisMat * basisInv) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [basisMat_mul_basisInv]; simp

theorem conjBlock_isometry (A : Matrix (Fin 2) (Fin 2) k) (hA : A.det = 1) :
    (basisMat * blockOne A * basisInv)ᵀ * (1 : Matrix (Fin 3) (Fin 3) k) *
      (basisMat * blockOne A * basisInv) = 1 := by
  calc (basisMat * blockOne A * basisInv)ᵀ * (1 : Matrix (Fin 3) (Fin 3) k) *
        (basisMat * blockOne A * basisInv)
      = basisInvᵀ * ((blockOne A)ᵀ * (basisMatᵀ * basisMat) * blockOne A) * basisInv := by
        simp only [Matrix.transpose_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = basisInvᵀ * gramMat * basisInv := by rw [basisMat_gram, blockOne_gram A hA]
    _ = 1 := basisInv_gram

theorem exists_blockOne_of_gram (D : Matrix (Fin 3) (Fin 3) k)
    (hD : Dᵀ * gramMat * D = gramMat) :
    ∃ A : Matrix (Fin 2) (Fin 2) k, A.det = 1 ∧ D = blockOne A := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have e : ∀ i j, (Dᵀ * (gramMat : Matrix (Fin 3) (Fin 3) k) * D) i j =
      (gramMat : Matrix (Fin 3) (Fin 3) k) i j := fun i j => by rw [hD]
  have e00 := e 0 0
  have e11 := e 1 1
  have e22 := e 2 2
  have e01 := e 0 1
  have e02 := e 0 2
  have e12 := e 1 2
  simp [Matrix.mul_apply, Fin.sum_univ_succ, gramMat] at e00 e11 e22 e01 e02 e12
  have ha : D 0 0 = 1 := by
    have : (D 0 0 - 1) ^ 2 = 0 := by
      linear_combination e00 + (1 - D 0 0 - D 2 0 * D 1 0) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  have hb0 : D 0 1 = 0 := by
    have : D 0 1 ^ 2 = 0 := by linear_combination e11 - (D 2 1 * D 1 1) * h2
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  have hb1 : D 0 2 = 0 := by
    have : D 0 2 ^ 2 = 0 := by linear_combination e22 - (D 2 2 * D 1 2) * h2
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  rw [ha, hb0] at e01
  rw [ha, hb1] at e02
  rw [hb0, hb1] at e12
  have hc0 : D 1 0 = 0 := by
    linear_combination (D 1 2) * e01 + (D 1 1) * e02 - (D 1 0) * e12 +
      (-(D 1 1 * D 1 2 * D 2 0)) * h2
  have hc1 : D 2 0 = 0 := by
    linear_combination (D 2 2) * e01 + (D 2 1) * e02 - (D 2 0) * e12 +
      (-(D 2 1 * D 2 2 * D 1 0)) * h2
  refine ⟨!![D 1 1, D 1 2; D 2 1, D 2 2], ?_, ?_⟩
  · rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination e12 + (-(D 1 2 * D 2 1)) * h2
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [blockOne, ha, hb0, hb1, hc0, hc1]

@[expose] def basisGL : GL (Fin 3) k :=
  ⟨basisMat, basisInv, basisMat_mul_basisInv, basisInv_mul_basisMat⟩

omit [CharP k 2] in
@[expose] def blockOneGL : Matrix.SpecialLinearGroup (Fin 2) k →* GL (Fin 3) k where
  toFun A := ⟨blockOne (A : Matrix (Fin 2) (Fin 2) k),
    blockOne ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k),
    by rw [← blockOne_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, blockOne_one],
    by rw [← blockOne_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, blockOne_one]⟩
  map_one' := Units.ext (by simp [blockOne_one])
  map_mul' A B := Units.ext (by simp [blockOne_mul])

@[expose] def sl2ToGL : Matrix.SpecialLinearGroup (Fin 2) k →* GL (Fin 3) k :=
  (MulAut.conj (basisGL (k := k))).toMonoidHom.comp blockOneGL

theorem coe_sl2ToGL (A : Matrix.SpecialLinearGroup (Fin 2) k) :
    ((sl2ToGL A : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      basisMat * blockOne (A : Matrix (Fin 2) (Fin 2) k) * basisInv := rfl

theorem trace_sl2ToGL (A : Matrix.SpecialLinearGroup (Fin 2) k) :
    Matrix.trace ((sl2ToGL A : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      1 + (A : Matrix (Fin 2) (Fin 2) k) 0 0 + (A : Matrix (Fin 2) (Fin 2) k) 1 1 := by
  rw [coe_sl2ToGL, Matrix.trace_mul_comm, ← Matrix.mul_assoc, basisInv_mul_basisMat,
    Matrix.one_mul]
  simp [Matrix.trace, Fin.sum_univ_succ, blockOne, add_assoc]

theorem sl2ToGL_mem (A : Matrix.SpecialLinearGroup (Fin 2) k) :
    sl2ToGL A ∈ matrixIsometryGroup (1 : Matrix (Fin 3) (Fin 3) k) := by
  rw [mem_matrixIsometryGroup, coe_sl2ToGL]
  exact conjBlock_isometry _ A.2

@[expose] def sl2ToIsometry :
    Matrix.SpecialLinearGroup (Fin 2) k →* matrixIsometryGroup (1 : Matrix (Fin 3) (Fin 3) k) :=
  sl2ToGL.codRestrict _ sl2ToGL_mem

theorem sl2ToIsometry_bijective :
    Function.Bijective (sl2ToIsometry (k := k)) := by
  refine ⟨(injective_iff_map_eq_one _).mpr fun A hA => ?_, fun g => ?_⟩
  · have h1 : ((sl2ToGL A : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1 :=
      congrArg (fun x : matrixIsometryGroup (1 : Matrix (Fin 3) (Fin 3) k) =>
        ((x : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) hA
    rw [coe_sl2ToGL] at h1
    have h2 : blockOne (A : Matrix (Fin 2) (Fin 2) k) = 1 := by
      calc blockOne (A : Matrix (Fin 2) (Fin 2) k)
          = (basisInv * basisMat) * blockOne (A : Matrix (Fin 2) (Fin 2) k) *
              (basisInv * basisMat) := by
            rw [basisInv_mul_basisMat, Matrix.one_mul, Matrix.mul_one]
        _ = basisInv * (basisMat * blockOne (A : Matrix (Fin 2) (Fin 2) k) * basisInv) *
              basisMat := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.mul_one, basisInv_mul_basisMat]
    apply Subtype.ext
    ext i j
    have := congrFun (congrFun h2 i.succ) j.succ
    fin_cases i <;> fin_cases j <;> simpa [blockOne, Matrix.one_apply] using this
  · obtain ⟨g, hg⟩ := g
    have hg' : ((g : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)ᵀ *
        ((g : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1 := by
      have := mem_matrixIsometryGroup.mp hg
      simpa using this
    set M : Matrix (Fin 3) (Fin 3) k := ((g : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) with hM
    have hHH' : (basisInv : Matrix (Fin 3) (Fin 3) k)ᵀ * basisMatᵀ = 1 := by
      rw [← Matrix.transpose_mul, basisMat_mul_basisInv, Matrix.transpose_one]
    have hD : (basisInv * M * basisMat)ᵀ * gramMat * (basisInv * M * basisMat) = gramMat := by
      calc (basisInv * M * basisMat)ᵀ * gramMat * (basisInv * M * basisMat)
          = basisMatᵀ * Mᵀ * (basisInvᵀ * basisMatᵀ) * (basisMat * basisInv) * M * basisMat := by
            rw [← basisMat_gram]
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = basisMatᵀ * (Mᵀ * M) * basisMat := by
            rw [hHH', basisMat_mul_basisInv]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = gramMat := by rw [hg', Matrix.mul_one, basisMat_gram]
    obtain ⟨A, hA, hDA⟩ := exists_blockOne_of_gram _ hD
    refine ⟨⟨A, hA⟩, Subtype.ext (Units.ext ?_)⟩
    change basisMat * blockOne A * basisInv = M
    rw [← hDA]
    calc basisMat * (basisInv * M * basisMat) * basisInv
        = (basisMat * basisInv) * M * (basisMat * basisInv) := by
          simp only [Matrix.mul_assoc]
      _ = M := by rw [basisMat_mul_basisInv, Matrix.one_mul, Matrix.mul_one]

@[expose] noncomputable def isometryThreeEquivSL2 :
    matrixIsometryGroup (1 : Matrix (Fin 3) (Fin 3) k) ≃* Matrix.SpecialLinearGroup (Fin 2) k :=
  (MulEquiv.ofBijective sl2ToIsometry sl2ToIsometry_bijective).symm

theorem sl2_center_eq_bot' : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) = ⊥ := by
  ext A
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Subgroup.mem_bot]
  constructor
  · rintro ⟨r, hr, hA⟩
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have hr1 : r = 1 := by
      have : (r - 1) ^ 2 = 0 := by
        linear_combination hr2 + (1 - r) * (CharTwo.two_eq_zero : (2 : k) = 0)
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    ext i j
    rw [← hA, hr1]
    simp [Matrix.one_apply]
  · rintro rfl
    exact ⟨1, by simp, by simp⟩

end O3

end CFSG.GH74.Uniqueness.Bender
