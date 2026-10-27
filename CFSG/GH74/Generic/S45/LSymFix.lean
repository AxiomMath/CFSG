module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation

public section

namespace CFSG.GH74.Generic.S45

open Matrix

theorem exists_congr_diagonal {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {m : ℕ}
    (B : Matrix (Fin m) (Fin m) F) (hB : B.IsSymm) :
    ∃ (P : Matrix (Fin m) (Fin m) F) (d : Fin m → F), IsUnit P.det ∧
      Pᵀ * B * P = Matrix.diagonal d := by
  classical
  have : Invertible (2 : F) := invertibleOfNonzero h2
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.1 (Matrix.isSymm_toBilin'_iff_isSymm.2 hB))
  let b : Module.Basis (Fin m) F (Fin m → F) := v.reindex (finCongr (Module.finrank_fin_fun F))
  let P : Matrix (Fin m) (Fin m) F := (Pi.basisFun F (Fin m)).toMatrix b
  have hPunit : IsUnit P.det := by
    have := (Pi.basisFun F (Fin m)).invertibleToMatrix b
    exact isUnit_det_of_invertible P
  have hb : Pᵀ * B * P = LinearMap.BilinForm.toMatrix b (Matrix.toBilin' B) := by
    have := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := Pi.basisFun F (Fin m)) b (Matrix.toBilin' B)
    rw [← this]
    congr 2
    exact (LinearMap.BilinForm.toMatrix'_toBilin' B).symm
  refine ⟨P, fun i => (Pᵀ * B * P) i i, hPunit, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Matrix.diagonal_apply_ne _ hij, hb, LinearMap.BilinForm.toMatrix_apply]
    have hne : (finCongr (Module.finrank_fin_fun F)).symm i ≠
        (finCongr (Module.finrank_fin_fun F)).symm j := fun h => hij (by simpa using h)
    have h0 := hv hne
    simpa [b, Module.Basis.reindex_apply] using h0

section Rot

variable {F : Type} [Field F] {m : ℕ}

@[expose] def rotT (j k : Fin m) (a : F) (l : Fin m) : F :=
  if l = j then -a⁻¹ else if l = k then a else 1

@[expose] def rotMat (j k : Fin m) (a : F) : Matrix (Fin m) (Fin m) F :=
  fun i l => if l = Equiv.swap j k i then rotT j k a l else 0

theorem rotMat_eq_perm_mul (j k : Fin m) (a : F) :
    rotMat j k a = (Equiv.swap j k).permMatrix F * Matrix.diagonal (rotT j k a) := by
  ext i l
  rw [Matrix.mul_diagonal]
  simp only [rotMat, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  by_cases h : l = Equiv.swap j k i
  · simp [h]
  · have : ¬ (Equiv.swap j k i = l) := fun h' => h h'.symm
    simp [h, this]

theorem det_rotMat {j k : Fin m} (hjk : j ≠ k) {a : F} (ha : a ≠ 0) : (rotMat j k a).det = 1 := by
  rw [rotMat_eq_perm_mul, Matrix.det_mul, Matrix.det_permutation, Matrix.det_diagonal,
    Equiv.Perm.sign_swap hjk]
  have h := Finset.prod_eq_mul (s := Finset.univ) (f := rotT j k a) j k hjk
    (fun c _ hc => by simp [rotT, hc.1, hc.2]) (fun h => absurd (Finset.mem_univ _) h)
    (fun h => absurd (Finset.mem_univ _) h)
  rw [h]
  simp [rotT, hjk.symm, ha]


theorem rotT_swap_mul {j k : Fin m} (hjk : j ≠ k) {a : F} (ha : a ≠ 0) (i : Fin m) :
    rotT j k a (Equiv.swap j k i) * rotT j k a i = if i = j ∨ i = k then -1 else 1 := by
  by_cases hij : i = j
  · subst hij
    simp [rotT, Equiv.swap_apply_left, hjk.symm, ha]
  · by_cases hik : i = k
    · subst hik
      simp [rotT, Equiv.swap_apply_right, hij, ha]
    · simp [rotT, Equiv.swap_apply_of_ne_of_ne hij hik, hij, hik]

theorem rotMat_mul_self {j k : Fin m} (hjk : j ≠ k) {a : F} (ha : a ≠ 0) :
    rotMat j k a * rotMat j k a =
      Matrix.diagonal (fun i => if i = j ∨ i = k then (-1 : F) else 1) := by
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (Equiv.swap j k i)]
  · by_cases hil : i = l
    · subst hil
      simp [rotMat, Matrix.diagonal_apply_eq, rotT_swap_mul hjk ha i]
    · rw [Matrix.diagonal_apply_ne _ hil]
      simp [rotMat, Ne.symm hil]
  · intro u _ hu
    simp [rotMat, hu]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem rotMat_diag {j k : Fin m} (hjk : j ≠ k) {a : F} (ha : a ≠ 0) (d : Fin m → F)
    (hd : d j = a * a * d k) :
    rotMat j k a * Matrix.diagonal d * (rotMat j k a)ᵀ = Matrix.diagonal d := by
  have key : ∀ i : Fin m, rotT j k a (Equiv.swap j k i) * rotT j k a (Equiv.swap j k i) *
      d (Equiv.swap j k i) = d i := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp [rotT, Equiv.swap_apply_left, hjk.symm, hd]
    · by_cases hik : i = k
      · subst hik
        simp [rotT, Equiv.swap_apply_right, hd]
        field_simp
      · simp [rotT, Equiv.swap_apply_of_ne_of_ne hij hik, hij, hik]
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (Equiv.swap j k i)]
  · by_cases hil : i = l
    · subst hil
      simp only [Matrix.mul_diagonal, Matrix.transpose_apply, rotMat, Matrix.diagonal_apply_eq]
      simp only [ite_true]
      rw [← key i]
      ring
    · rw [Matrix.diagonal_apply_ne _ hil]
      simp only [Matrix.mul_diagonal, Matrix.transpose_apply, rotMat]
      have : ¬ (Equiv.swap j k i = Equiv.swap j k l) := fun h => hil ((Equiv.injective _) h)
      simp [this]
  · intro u _ hu
    simp [Matrix.mul_diagonal, rotMat, hu]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Rot

theorem exists_same_square_class {F : Type} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
    (hm : 3 ≤ m) (d : Fin m → F) (hd : ∀ i, d i ≠ 0) :
    ∃ j k : Fin m, j ≠ k ∧ ∃ a : F, d j = a * a * d k := by
  classical
  obtain ⟨j, k, hjk, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin m => decide (quadraticChar F (d i) = 1)) (by simp; omega)
  refine ⟨j, k, hjk, ?_⟩
  have hdk := hd k
  have hdj := hd j
  by_cases h1 : quadraticChar F (d j) = 1
  · have h2 : quadraticChar F (d k) = 1 := by simpa [h1] using hf.symm
    obtain ⟨u, hu⟩ := (quadraticChar_one_iff_isSquare hdj).1 h1
    obtain ⟨v, hv⟩ := (quadraticChar_one_iff_isSquare hdk).1 h2
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv; exact hdk hv
    refine ⟨u / v, ?_⟩
    rw [hu, hv]
    field_simp
  · have h1' : quadraticChar F (d j) = -1 := (quadraticChar_dichotomy hdj).resolve_left h1
    have h2' : quadraticChar F (d k) = -1 := by
      rcases quadraticChar_dichotomy hdk with h | h
      · exfalso
        apply h1
        simpa [h] using hf
      · exact h
    have hprod : quadraticChar F (d j * d k) = 1 := by
      rw [map_mul, h1', h2']
      norm_num
    obtain ⟨w, hw⟩ := (quadraticChar_one_iff_isSquare (mul_ne_zero hdj hdk)).1 hprod
    refine ⟨w / d k, ?_⟩
    field_simp
    rw [hw]
    ring

theorem exists_isometry_order_four {F : Type} [Field F] [Fintype F] [DecidableEq F] (h2 : (2 : F) ≠ 0) {m : ℕ}
    (hm : 3 ≤ m) (B : Matrix (Fin m) (Fin m) F) (hB : B.IsSymm) (hBdet : IsUnit B.det) :
    ∃ c : Matrix (Fin m) (Fin m) F, c.det = 1 ∧ c * B * cᵀ = B ∧
      (∀ l : F, c * c ≠ l • (1 : Matrix (Fin m) (Fin m) F)) ∧ c * c * (c * c) = 1 := by
  classical
  obtain ⟨P, d, hP, hPd⟩ := exists_congr_diagonal h2 B hB
  have hdet : (Matrix.diagonal d).det ≠ 0 := by
    rw [← hPd, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hP.ne_zero hBdet.ne_zero) hP.ne_zero
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    rw [Matrix.det_diagonal] at hdet
    exact (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)
  obtain ⟨j, k, hjk, a, ha⟩ := exists_same_square_class hm d hd
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hd j (by simpa using ha)
  obtain ⟨i0, hi0j, hi0k⟩ : ∃ i0 : Fin m, i0 ≠ j ∧ i0 ≠ k := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin m)) ⊆ {j, k} := fun i _ => by
      by_cases hij : i = j
      · simp [hij]
      · simp [hcon i hij]
    have := Finset.card_le_card hsub
    have h2' : ({j, k} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  let R : Matrix (Fin m) (Fin m) F := rotMat j k a
  have hR1 : R * Matrix.diagonal d * Rᵀ = Matrix.diagonal d := rotMat_diag hjk ha0 d ha
  have hR2 : R * R = Matrix.diagonal (fun i => if i = j ∨ i = k then (-1 : F) else 1) :=
    rotMat_mul_self hjk ha0
  have hRdet : R.det = 1 := det_rotMat hjk ha0
  let Q : Matrix (Fin m) (Fin m) F := (P⁻¹)ᵀ
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hQP : Q * Pᵀ = 1 := by
    rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  have hPQ : Pᵀ * Q = 1 := by
    rw [← Matrix.transpose_mul, hPP', Matrix.transpose_one]
  have hRR : R * R * (R * R) = 1 := by
    rw [hR2, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    by_cases h : i = j ∨ i = k <;> simp [h]
  refine ⟨Q * R * Pᵀ, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, hRdet, mul_one, ← Matrix.det_mul, hQP, Matrix.det_one]
  ·
    have hB' : Q * (Pᵀ * B * P) * Qᵀ = B := by
      calc Q * (Pᵀ * B * P) * Qᵀ = (Q * Pᵀ) * B * (P * P⁻¹) := by
            simp only [Q, Matrix.transpose_transpose, Matrix.mul_assoc]
        _ = B := by rw [hQP, hPP, Matrix.one_mul, Matrix.mul_one]
    calc Q * R * Pᵀ * B * (Q * R * Pᵀ)ᵀ
        = Q * (R * (Pᵀ * B * P) * Rᵀ) * Qᵀ := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = Q * (Pᵀ * B * P) * Qᵀ := by rw [hPd, hR1]
      _ = B := hB'
  · intro l hl
    have h1 : Q * R * Pᵀ * (Q * R * Pᵀ) = Q * (R * R) * Pᵀ := by
      calc Q * R * Pᵀ * (Q * R * Pᵀ) = Q * R * (Pᵀ * Q) * R * Pᵀ := by
            simp only [Matrix.mul_assoc]
        _ = Q * (R * R) * Pᵀ := by rw [hPQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [h1, hR2] at hl
    have h2' : Matrix.diagonal (fun i => if i = j ∨ i = k then (-1 : F) else 1) =
        l • (1 : Matrix (Fin m) (Fin m) F) := by
      calc Matrix.diagonal (fun i => if i = j ∨ i = k then (-1 : F) else 1)
          = (Pᵀ * Q) * Matrix.diagonal (fun i => if i = j ∨ i = k then (-1 : F) else 1) * (Pᵀ * Q) := by
            rw [hPQ, Matrix.one_mul, Matrix.mul_one]
        _ = Pᵀ * (Q * Matrix.diagonal (fun i => if i = j ∨ i = k then (-1 : F) else 1) * Pᵀ) * Q := by
            simp only [Matrix.mul_assoc]
        _ = Pᵀ * (l • (1 : Matrix (Fin m) (Fin m) F)) * Q := by rw [hl]
        _ = l • (Pᵀ * Q) := by
            rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
        _ = l • (1 : Matrix (Fin m) (Fin m) F) := by rw [hPQ]
    have e1 := congrFun (congrFun h2' j) j
    have e2 := congrFun (congrFun h2' i0) i0
    simp [Matrix.diagonal_apply_eq, Matrix.smul_apply, hi0j, hi0k] at e1 e2
    apply h2
    linear_combination e2 - e1
  · have h1 : Q * R * Pᵀ * (Q * R * Pᵀ) = Q * (R * R) * Pᵀ := by
      calc Q * R * Pᵀ * (Q * R * Pᵀ) = Q * R * (Pᵀ * Q) * R * Pᵀ := by
            simp only [Matrix.mul_assoc]
        _ = Q * (R * R) * Pᵀ := by rw [hPQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [h1]
    calc Q * (R * R) * Pᵀ * (Q * (R * R) * Pᵀ) = Q * (R * R) * (Pᵀ * Q) * (R * R) * Pᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hPQ, Matrix.mul_one, show Q * (R * R) * (R * R) * Pᵀ = Q * (R * R * (R * R)) * Pᵀ by
            simp only [Matrix.mul_assoc], hRR, Matrix.mul_one, hQP]

end CFSG.GH74.Generic.S45
