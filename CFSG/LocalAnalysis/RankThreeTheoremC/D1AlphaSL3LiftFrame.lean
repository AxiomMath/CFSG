module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftCubes
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftEigen
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftDiag

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift

open Matrix

theorem prod_sub_cube_roots {k : Type*} [Field k] (M : Matrix (Fin 3) (Fin 3) k) {η w : k}
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (hM : M ^ 3 = (η ^ 3) • (1 : Matrix (Fin 3) (Fin 3) k)) :
    (M - (η * w ^ (0 : Fin 3).val) • (1 : Matrix (Fin 3) (Fin 3) k)) *
      (M - (η * w ^ (1 : Fin 3).val) • 1) * (M - (η * w ^ (2 : Fin 3).val) • 1) = 0 := by
  have hw2 : w ^ 2 + w + 1 = 0 := by
    have : (w - 1) * (w ^ 2 + w + 1) = 0 := by linear_combination hw3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hw1
    · exact h
  have hpoly : ((Polynomial.X - Polynomial.C (η * w ^ (0 : Fin 3).val)) *
      (Polynomial.X - Polynomial.C (η * w ^ (1 : Fin 3).val)) *
      (Polynomial.X - Polynomial.C (η * w ^ (2 : Fin 3).val)) : Polynomial k) =
      Polynomial.X ^ 3 - Polynomial.C (η ^ 3) := by
    have h3 : (Polynomial.C w) ^ 3 = 1 := by rw [← map_pow, hw3, map_one]
    have h2 : (Polynomial.C w) ^ 2 + Polynomial.C w + 1 = 0 := by
      rw [← map_pow, ← map_add, ← map_one (Polynomial.C (R := k)), ← map_add, hw2, map_zero]
    simp only [map_mul, map_pow, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
      mul_one]
    linear_combination (-(Polynomial.C η) * Polynomial.X ^ 2 +
      (Polynomial.C η) ^ 2 * Polynomial.X) * h2 +
      ((Polynomial.C η) ^ 2 * Polynomial.X - (Polynomial.C η) ^ 3) * h3
  have := congrArg (Polynomial.aeval M) hpoly
  rw [map_mul, map_mul, map_sub, map_sub, map_sub, map_sub, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hM, sub_self] at this
  exact this

theorem injective_cube_roots {k : Type*} [Field k] {η w : k} (hη : η ≠ 0) (hw3 : w ^ 3 = 1)
    (hw1 : w ≠ 1) : Function.Injective (fun j : Fin 3 => η * w ^ j.val) := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    norm_num at hw3
  have hw2 : w ^ 2 ≠ 1 := by
    intro h
    apply hw1
    calc w = w ^ 3 * (w ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [hw3, h]; simp
  have hww : w ^ 2 ≠ w := by
    intro h
    apply hw1
    have : w * (w - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hw0
    · exact sub_eq_zero.mp h'
  intro i j hij
  simp only at hij
  have h := mul_left_cancel₀ hη hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem exists_common_frame {k : Type*} [Field k] {w : k} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (s g : GL (Fin 3) k) (hsg : (s : Matrix (Fin 3) (Fin 3) k) * g = g * s)
    (hdet : (s : Matrix (Fin 3) (Fin 3) k).det = 1) {ζ μ : k}
    (hs3 : (s : Matrix (Fin 3) (Fin 3) k) ^ 3 = ζ • (1 : Matrix (Fin 3) (Fin 3) k))
    (hg3 : (g : Matrix (Fin 3) (Fin 3) k) ^ 3 = μ • (1 : Matrix (Fin 3) (Fin 3) k))
    (hns : ∀ c : k, (s : Matrix (Fin 3) (Fin 3) k) ≠ c • 1) :
    ∃ (P : GL (Fin 3) k) (u v : Fin 3 → k),
      ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) *
        (P : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal u ∧
      ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k) *
        (P : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal v := by
  obtain ⟨η, hη⟩ := exists_cube_root_of_det_one _ hdet hs3
  have hsη : (s : Matrix (Fin 3) (Fin 3) k) ^ 3 =
      (η ^ 3) • (1 : Matrix (Fin 3) (Fin 3) k) := by
    rw [hη]; exact hs3
  have hη0 : η ≠ 0 := by
    rintro rfl
    have := congrArg Matrix.det hsη
    simp [hdet] at this
  have hs_prod := prod_sub_cube_roots _ hw3 hw1 hsη
  obtain ⟨b, hb⟩ := exists_cube_root_of_commute _ _ hsg (fun j : Fin 3 => η * w ^ j.val) hs_prod
    hns hg3
  have hgb : (g : Matrix (Fin 3) (Fin 3) k) ^ 3 = (b ^ 3) • (1 : Matrix (Fin 3) (Fin 3) k) := by
    rw [hb]; exact hg3
  have hb0 : b ≠ 0 := by
    rintro rfl
    have := congrArg Matrix.det hgb
    have hd : (g : Matrix (Fin 3) (Fin 3) k).det ≠ 0 := by
      have := g.det.ne_zero
      simpa [Matrix.GeneralLinearGroup.det] using this
    simp [Matrix.det_pow] at this
    exact hd this
  have hg_prod := prod_sub_cube_roots _ hw3 hw1 hgb
  obtain ⟨P, u, v, hu, hv⟩ := exists_joint_diagonal (s : Matrix (Fin 3) (Fin 3) k) g hsg
    (fun j : Fin 3 => η * w ^ j.val) (fun j : Fin 3 => b * w ^ j.val)
    (injective_cube_roots hη0 hw3 hw1) (injective_cube_roots hb0 hw3 hw1) hs_prod hg_prod
  exact ⟨P, u, v, hu, hv⟩

@[expose] def IsConjBy {k : Type*} [Field k] (σ : MulAut (SpecialLinearGroup (Fin 3) k))
    (M : GL (Fin 3) k) : Prop :=
  ∀ t : SpecialLinearGroup (Fin 3) k,
    ((σ t : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      (M : Matrix (Fin 3) (Fin 3) k) * (t : Matrix (Fin 3) (Fin 3) k) *
        ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)

theorem IsConjBy.mul {k : Type*} [Field k] {σ τ : MulAut (SpecialLinearGroup (Fin 3) k)}
    {M N : GL (Fin 3) k} (hσ : IsConjBy σ M) (hτ : IsConjBy τ N) :
    IsConjBy (σ * τ) (M * N) := by
  intro t
  have h1 : ((σ * τ) t : SpecialLinearGroup (Fin 3) k) = σ (τ t) := rfl
  rw [h1, hσ, hτ]
  simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem IsConjBy.pow {k : Type*} [Field k] {σ : MulAut (SpecialLinearGroup (Fin 3) k)}
    {M : GL (Fin 3) k} (hσ : IsConjBy σ M) (n : ℕ) : IsConjBy (σ ^ n) (M ^ n) := by
  induction n with
  | zero =>
    intro t
    simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hσ

theorem IsConjBy.fix {k : Type*} [Field k] {σ : MulAut (SpecialLinearGroup (Fin 3) k)}
    {M : GL (Fin 3) k} (h : IsConjBy σ M) {x : SpecialLinearGroup (Fin 3) k}
    (hx : (M : Matrix (Fin 3) (Fin 3) k) * (x : Matrix (Fin 3) (Fin 3) k) =
      (x : Matrix (Fin 3) (Fin 3) k) * (M : Matrix (Fin 3) (Fin 3) k)) : σ x = x := by
  apply Subtype.ext
  rw [h x, hx, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem comm_of_conj_eq {k : Type*} [Field k] {M : GL (Fin 3) k}
    {T : Matrix (Fin 3) (Fin 3) k}
    (h : T = (M : Matrix (Fin 3) (Fin 3) k) * T *
      ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) :
    (M : Matrix (Fin 3) (Fin 3) k) * T = T * (M : Matrix (Fin 3) (Fin 3) k) := by
  have h2 : T * (M : Matrix (Fin 3) (Fin 3) k) = (M : Matrix (Fin 3) (Fin 3) k) * T := by
    calc T * (M : Matrix (Fin 3) (Fin 3) k)
        = ((M : Matrix (Fin 3) (Fin 3) k) * T *
            ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) *
          (M : Matrix (Fin 3) (Fin 3) k) := by rw [← h]
      _ = (M : Matrix (Fin 3) (Fin 3) k) * T := by
        rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  exact h2.symm

theorem conj_eq_self_of_comm {k : Type*} [Field k] {M : GL (Fin 3) k}
    {T : Matrix (Fin 3) (Fin 3) k}
    (h : (M : Matrix (Fin 3) (Fin 3) k) * T = T * (M : Matrix (Fin 3) (Fin 3) k)) :
    (M : Matrix (Fin 3) (Fin 3) k) * T *
      ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = T := by
  rw [h, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem diag_cube_of_conj {k : Type*} [Field k] (P M : GL (Fin 3) k) (d : Fin 3 → k) (c : k)
    (hM : (M : Matrix (Fin 3) (Fin 3) k) ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) k))
    (hd : ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (M : Matrix (Fin 3) (Fin 3) k) *
      (P : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal d) (a : Fin 3) : d a ^ 3 = c := by
  have h1 : ((P⁻¹ * M * P : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal d := by
    rw [← hd]; simp [Units.val_mul]
  have h2 : (P⁻¹ * M * P) ^ 3 = P⁻¹ * M ^ 3 * P := by
    have := conj_pow (a := P⁻¹) (b := M) (i := 3)
    simpa using this
  have h3 : (Matrix.diagonal d) ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) k) := by
    rw [← h1, ← Units.val_pow_eq_pow_val, h2]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, hM]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  rw [Matrix.diagonal_pow] at h3
  have := congrFun (congrFun h3 a) a
  simpa using this

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
