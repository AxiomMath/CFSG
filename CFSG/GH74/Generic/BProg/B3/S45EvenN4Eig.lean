module

public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.GH74.Generic.BProg.B3.S45EvenN4Eig

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification

variable {F : Type} [Field F]

theorem isPrimitiveRoot_neg_one (h2 : (2 : F) ≠ 0) : IsPrimitiveRoot (-1 : F) 2 := by
  refine ⟨by norm_num, fun l hl => ?_⟩
  by_contra hodd
  have hodd' : Odd l := Nat.odd_iff.2 (by omega)
  rw [hodd'.neg_one_pow] at hl
  apply h2
  linear_combination -hl

theorem exists_eigen_diag (h2 : (2 : F) ≠ 0) {T : Matrix (Fin 4) (Fin 4) F} (hT : T * T = 1) :
    ∃ (P Q : Matrix (Fin 4) (Fin 4) F) (μ : Fin 4 → F), P * Q = 1 ∧ Q * P = 1 ∧
      T * P = P * diagonal μ ∧ ∀ j, μ j = 1 ∨ μ j = -1 := by
  classical
  have hζ := isPrimitiveRoot_neg_one h2
  let f : Unit → End F (Fin 4 → F) := fun _ => Matrix.toLinAlgEquiv' T
  have hfp : ∀ i, f i ^ 2 = 1 := fun i => by
    show Matrix.toLinAlgEquiv' T ^ 2 = 1
    rw [pow_two, ← map_mul, hT, map_one]
  obtain ⟨b, μ, hb⟩ := CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one hζ f
    (fun _ _ => Commute.refl _) hfp
  let e := finCongr (Module.finrank_fin_fun (n := 4) F)
  let b' : Basis (Fin 4) F (Fin 4 → F) := b.reindex e
  have hb' : ∀ j, T *ᵥ (b' j) = μ () (e.symm j) • b' j := fun j => by
    have := hb () (e.symm j)
    simpa [f, b', Basis.reindex_apply] using this
  let P : Matrix (Fin 4) (Fin 4) F := (Pi.basisFun F (Fin 4)).toMatrix b'
  have hPi : Invertible P := Basis.invertibleToMatrix (Pi.basisFun F (Fin 4)) b'
  have hTP : T * P = P * diagonal (fun j => μ () (e.symm j)) := by
    ext a j
    have h := congrFun (hb' j) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_diagonal]
    simp only [P, Matrix.mul_apply, Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [h, mul_comm]
  have hPQ : P * ⅟P = 1 := mul_invOf_self P
  have hQP : ⅟P * P = 1 := invOf_mul_self P
  have hD : diagonal (fun j => μ () (e.symm j)) = ⅟P * T * P := by
    rw [Matrix.mul_assoc, hTP, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  refine ⟨P, ⅟P, fun j => μ () (e.symm j), hPQ, hQP, hTP, fun j => ?_⟩
  have hDD : diagonal (fun j => μ () (e.symm j)) * diagonal (fun j => μ () (e.symm j)) = 1 := by
    calc diagonal (fun j => μ () (e.symm j)) * diagonal (fun j => μ () (e.symm j))
        = (⅟P * T * P) * (⅟P * T * P) := by rw [← hD]
      _ = ⅟P * (T * (P * ⅟P) * T) * P := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPQ, Matrix.mul_one, hT, Matrix.mul_one, hQP]
  have hjj : μ () (e.symm j) * μ () (e.symm j) = 1 := by
    have := congrFun (congrFun hDD j) j
    simpa [Matrix.mul_apply, Matrix.diagonal_apply] using this
  exact mul_self_eq_one_iff.1 hjj

theorem submatrix_perm_facts (σ : Equiv.Perm (Fin 4)) {P Q T : Matrix (Fin 4) (Fin 4) F}
    {μ : Fin 4 → F} (hPQ : P * Q = 1) (hQP : Q * P = 1) (hTP : T * P = P * diagonal μ) :
    P.submatrix id σ * Q.submatrix σ id = 1 ∧ Q.submatrix σ id * P.submatrix id σ = 1 ∧
      T * P.submatrix id σ = P.submatrix id σ * diagonal (μ ∘ σ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.submatrix_mul P Q id σ id σ.bijective, hPQ, Matrix.submatrix_id_id]
  · rw [← Matrix.submatrix_mul Q P σ id σ Function.bijective_id, hQP, Matrix.submatrix_one_equiv]
  · have h1 : T * P.submatrix id σ = (T * P).submatrix id σ := by
      rw [Matrix.submatrix_mul T P id id σ Function.bijective_id]
      simp
    rw [h1, hTP, Matrix.submatrix_mul P (diagonal μ) id σ σ σ.bijective,
      Matrix.submatrix_diagonal_equiv]

theorem exists_perm_eq {μ : Fin 4 → F} (hμ : ∀ j, μ j = 1 ∨ μ j = -1) :
    ∃ σ : Equiv.Perm (Fin 4), μ (σ 0) = μ (σ 1) := by
  classical
  obtain ⟨i, j, hij, hβ⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun j : Fin 4 => decide (μ j = 1))
    (by simp)
  have hμij : μ i = μ j := by
    simp only [decide_eq_decide] at hβ
    by_cases hi : μ i = 1
    · rw [hi, (hβ.1 hi)]
    · have hi' : μ i = -1 := (hμ i).resolve_left hi
      have hj : ¬ μ j = 1 := fun hj => hi (hβ.2 hj)
      rw [hi', (hμ j).resolve_left hj]
  have hperm : ∀ i j : Fin 4, i ≠ j → ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by decide
  obtain ⟨σ, hσ0, hσ1⟩ := hperm i j hij
  exact ⟨σ, by rw [hσ0, hσ1]; exact hμij⟩

theorem diagonal_perm_pair {μ : Fin 4 → F} {σ : Equiv.Perm (Fin 4)} (h : μ (σ 0) = μ (σ 1)) :
    diagonal (μ ∘ σ) = diagonal ![μ (σ 0), μ (σ 0), μ (σ 2), μ (σ 3)] := by
  congr 1
  funext c
  fin_cases c
  · rfl
  · simp [h]
  · rfl
  · rfl

theorem exists_eigen_pair (h2 : (2 : F) ≠ 0) {T : Matrix (Fin 4) (Fin 4) F} (hT : T * T = 1) :
    ∃ (P Q : Matrix (Fin 4) (Fin 4) F) (m n k : F), P * Q = 1 ∧ Q * P = 1 ∧
      T * P = P * diagonal ![m, m, n, k] := by
  obtain ⟨P, Q, μ, hPQ, hQP, hTP, hμ⟩ := exists_eigen_diag h2 hT
  obtain ⟨σ, hσ⟩ := exists_perm_eq hμ
  obtain ⟨h1, h2', h3⟩ := submatrix_perm_facts σ hPQ hQP hTP
  exact ⟨P.submatrix id σ, Q.submatrix σ id, μ (σ 0), μ (σ 2), μ (σ 3), h1, h2',
    by rw [h3, diagonal_perm_pair hσ]⟩

@[expose] def ar : Matrix (Fin 4) (Fin 4) F := !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def br : Matrix (Fin 4) (Fin 4) F := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]

theorem ar_det : (ar : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [ar, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero]
  rfl

theorem br_det : (br : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [br, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero]
  rfl

theorem ar_pow : (ar : Matrix (Fin 4) (Fin 4) F) * ar * (ar * ar) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ar, Matrix.mul_apply, Fin.sum_univ_four]

theorem ar_sq_ne (h2 : (2 : F) ≠ 0) : (ar : Matrix (Fin 4) (Fin 4) F) * ar ≠ 1 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [ar, Matrix.mul_apply, Fin.sum_univ_four] at this
  apply h2
  linear_combination -this

theorem br_sq : (br : Matrix (Fin 4) (Fin 4) F) * br = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [br, Matrix.mul_apply, Fin.sum_univ_four]

theorem br_ar_br : (br : Matrix (Fin 4) (Fin 4) F) * ar * br * ar = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [br, ar, Matrix.mul_apply, Fin.sum_univ_four]

theorem ar_diag (m n k : F) :
    (ar : Matrix (Fin 4) (Fin 4) F) * diagonal ![m, m, n, k] = diagonal ![m, m, n, k] * ar := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ar, Matrix.mul_apply, Matrix.diagonal_apply]

theorem br_diag (m n k : F) :
    (br : Matrix (Fin 4) (Fin 4) F) * diagonal ![m, m, n, k] = diagonal ![m, m, n, k] * br := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [br, Matrix.mul_apply, Matrix.diagonal_apply]

@[expose] def arSL : Matrix.SpecialLinearGroup (Fin 4) F := ⟨ar, ar_det⟩

@[expose] def brSL : Matrix.SpecialLinearGroup (Fin 4) F := ⟨br, br_det⟩

theorem arSL_pow : (arSL : Matrix.SpecialLinearGroup (Fin 4) F) ^ 4 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  show (ar : Matrix (Fin 4) (Fin 4) F) ^ 4 = 1
  calc (ar : Matrix (Fin 4) (Fin 4) F) ^ 4 = ar * ar * (ar * ar) := by
        simp [pow_succ, Matrix.mul_assoc]
    _ = 1 := ar_pow

theorem arSL_sq_ne (h2 : (2 : F) ≠ 0) : (arSL : Matrix.SpecialLinearGroup (Fin 4) F) ^ 2 ≠ 1 := by
  intro h
  apply ar_sq_ne h2
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) h
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at this
  rw [pow_two] at this
  exact this

theorem brSL_sq : (brSL : Matrix.SpecialLinearGroup (Fin 4) F) * brSL = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  exact br_sq

theorem brSL_arSL : (brSL : Matrix.SpecialLinearGroup (Fin 4) F) * arSL * (brSL)⁻¹ = (arSL)⁻¹ := by
  have hb : (brSL : Matrix.SpecialLinearGroup (Fin 4) F)⁻¹ = brSL :=
    inv_eq_of_mul_eq_one_right brSL_sq
  rw [hb, eq_inv_iff_mul_eq_one]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  exact br_ar_br

theorem conj_comm {P Q T D M : Matrix (Fin 4) (Fin 4) F} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hTP : T * P = P * D) (hM : M * D = D * M) : (P * M * Q) * T = T * (P * M * Q) := by
  have hT' : T = P * D * Q := by
    calc T = T * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = (T * P) * Q := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hTP]
  rw [hT']
  calc P * M * Q * (P * D * Q) = P * M * (Q * P) * D * Q := by simp only [Matrix.mul_assoc]
    _ = P * (M * D) * Q := by rw [hQP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = P * (D * M) * Q := by rw [hM]
    _ = P * D * (Q * P) * M * Q := by rw [hQP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_D8_comm (h2 : (2 : F) ≠ 0) {T : Matrix (Fin 4) (Fin 4) F} (hT : T * T = 1) :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 4) F,
      (a : Matrix (Fin 4) (Fin 4) F) * T = T * a ∧ (b : Matrix (Fin 4) (Fin 4) F) * T = T * b ∧
        a ^ 4 = 1 ∧ a ^ 2 ≠ 1 ∧ b * b = 1 ∧ b * a * b⁻¹ = a⁻¹ := by
  obtain ⟨P, Q, m, n, k, hPQ, hQP, hTP⟩ := exists_eigen_pair h2 hT
  let Pg : GL (Fin 4) F := ⟨P, Q, hPQ, hQP⟩
  let φ := CatalogueBHigherLinearAction.slConjugation 4 F Pg
  have hcoe : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((φ g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = P * g * Q :=
    fun g => LinearFlag.coe_slConjugation Pg g
  refine ⟨φ arSL, φ brSL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcoe]; exact conj_comm hPQ hQP hTP (ar_diag m n k)
  · rw [hcoe]; exact conj_comm hPQ hQP hTP (br_diag m n k)
  · rw [← map_pow, arSL_pow, map_one]
  · intro h
    apply arSL_sq_ne h2
    apply φ.injective
    rw [map_pow, h, map_one]
  · rw [← map_mul, brSL_sq, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, brSL_arSL, map_inv]

end CFSG.GH74.Generic.BProg.B3.S45EvenN4Eig
