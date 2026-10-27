module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitNormalization

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

open Matrix QuadraticMap

variable {K : Type*} [Field K]

theorem linearEquiv_ext_matrixUnit
    {f h : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K}
    (he : ∀ i j, f (matrixUnit i j) = h (matrixUnit i j)) : f = h := by
  apply LinearEquiv.ext
  intro X
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : Matrix.single i j (X i j) = X i j • matrixUnit (K := K) i j := by
    simp [matrixUnit, Matrix.smul_single]
  rw [hs, map_smul, map_smul, he]

theorem normalized_fixes_second_projector (g : DeterminantIsometries K)
    (h1 : g.val 1 = 1) (he : g.val (matrixUnit 0 0) = matrixUnit 0 0) :
    g.val (matrixUnit 1 1) = matrixUnit 1 1 := by
  have hE : matrixUnit (K := K) 1 1 = 1 - matrixUnit 0 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrixUnit, Matrix.single]
  rw [hE, map_sub, h1, he]

private theorem normalized_offdiagonal_zero (g : DeterminantIsometries K)
    (h1 : g.val 1 = 1) (he : g.val (matrixUnit 0 0) = matrixUnit 0 0)
    (i j : Fin 2) (hij : i ≠ j) :
    g.val (matrixUnit i j) 0 0 = 0 ∧ g.val (matrixUnit i j) 1 1 = 0 := by
  have hp := determinantIsometry_polar g (matrixUnit 0 0) (matrixUnit i j)
  rw [he] at hp
  have h11 : g.val (matrixUnit i j) 1 1 = 0 := by
    fin_cases i <;> fin_cases j <;> simp_all [determinantForm_polar, matrixUnit, Matrix.single]
  have ht := determinantIsometry_trace g h1 (matrixUnit i j)
  have h00 : g.val (matrixUnit i j) 0 0 = 0 := by
    rw [Matrix.trace_fin_two, h11, add_zero] at ht
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.trace_fin_two, matrixUnit, Matrix.single]
  exact ⟨h00, h11⟩

theorem normalized_offdiagonal_dichotomy (g : DeterminantIsometries K)
    (h1 : g.val 1 = 1) (he : g.val (matrixUnit 0 0) = matrixUnit 0 0) :
    ∃ c : Kˣ,
      (g.val (matrixUnit 0 1) = (c : K) • matrixUnit 0 1 ∧
        g.val (matrixUnit 1 0) = (c⁻¹ : Kˣ).val • matrixUnit 1 0) ∨
      (g.val (matrixUnit 0 1) = (c⁻¹ : Kˣ).val • matrixUnit 1 0 ∧
        g.val (matrixUnit 1 0) = (c : K) • matrixUnit 0 1) := by
  let F := g.val (matrixUnit 0 1)
  let G := g.val (matrixUnit 1 0)
  obtain ⟨hf00, hf11⟩ := normalized_offdiagonal_zero g h1 he 0 1 (by decide)
  obtain ⟨hg00, hg11⟩ := normalized_offdiagonal_zero g h1 he 1 0 (by decide)
  change F 0 0 = 0 at hf00
  change F 1 1 = 0 at hf11
  change G 0 0 = 0 at hg00
  change G 1 1 = 0 at hg11
  have hf : F 0 1 * F 1 0 = 0 := by
    have hd := determinantIsometry_det g (matrixUnit 0 1)
    rw [matrixUnit_det, Matrix.det_fin_two] at hd
    change F 0 0 * F 1 1 - F 0 1 * F 1 0 = 0 at hd
    simpa [hf00, hf11] using hd
  have hg : G 0 1 * G 1 0 = 0 := by
    have hd := determinantIsometry_det g (matrixUnit 1 0)
    rw [matrixUnit_det, Matrix.det_fin_two] at hd
    change G 0 0 * G 1 1 - G 0 1 * G 1 0 = 0 at hd
    simpa [hg00, hg11] using hd
  have hfg : F 0 1 * G 1 0 + F 1 0 * G 0 1 = 1 := by
    have hp := determinantIsometry_polar g (matrixUnit 0 1) (matrixUnit 1 0)
    rw [determinantForm_polar, determinantForm_polar] at hp
    change F 0 0 * G 1 1 + F 1 1 * G 0 0 - F 0 1 * G 1 0 - F 1 0 * G 0 1 = _ at hp
    simp [hf00, hf11, matrixUnit, Matrix.single] at hp
    linear_combination -hp
  by_cases hf01 : F 0 1 = 0
  · have hprod : F 1 0 * G 0 1 = 1 := by simpa [hf01] using hfg
    have hg01 : G 0 1 ≠ 0 := by intro h; simp [h] at hprod
    have hg10 : G 1 0 = 0 := (mul_eq_zero.mp hg).resolve_left hg01
    have hf10 : F 1 0 = (G 0 1)⁻¹ := by
      rw [← one_div]
      apply (eq_div_iff hg01).mpr
      simpa using hprod
    refine ⟨Units.mk0 (G 0 1) hg01, Or.inr ⟨?_, ?_⟩⟩
    · change F = (Units.mk0 (G 0 1) hg01)⁻¹.val • matrixUnit 1 0
      ext i j
      fin_cases i <;> fin_cases j <;> simp [matrixUnit, Matrix.single, hf00, hf11, hf01, hf10]
    · change G = G 0 1 • matrixUnit 0 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [matrixUnit, Matrix.single, hg00, hg11, hg10]
  · have hf10 : F 1 0 = 0 := (mul_eq_zero.mp hf).resolve_left hf01
    have hprod : F 0 1 * G 1 0 = 1 := by simpa [hf10] using hfg
    have hg10 : G 1 0 ≠ 0 := by intro h; simp [h] at hprod
    have hg01 : G 0 1 = 0 := (mul_eq_zero.mp hg).resolve_right hg10
    have heq : G 1 0 = (F 0 1)⁻¹ := by
      rw [← one_div]
      apply (eq_div_iff hf01).mpr
      simpa [mul_comm] using hprod
    refine ⟨Units.mk0 (F 0 1) hf01, Or.inl ⟨?_, ?_⟩⟩
    · change F = F 0 1 • matrixUnit 0 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [matrixUnit, Matrix.single, hf00, hf11, hf10]
    · change G = (Units.mk0 (F 0 1) hf01)⁻¹.val • matrixUnit 1 0
      ext i j
      fin_cases i <;> fin_cases j <;> simp [matrixUnit, Matrix.single, hg00, hg11, hg01, heq]

@[expose] def diagonalUnit (c : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K where
  val := !![(c : K), 0; 0, 1]
  inv := !![(c⁻¹ : Kˣ).val, 0; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem rho_diagonalUnit_matrixUnit (c : Kˣ) (i j : Fin 2) :
    (rho (conjugationPair (diagonalUnit c))).val (matrixUnit i j) =
      (if i = j then 1 else if i = 0 then (c : K) else (c⁻¹ : Kˣ).val) • matrixUnit i j := by
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [rho_apply, conjugationPair, diagonalUnit, matrixUnit, Matrix.single,
      Matrix.mul_apply, Matrix.vecHead, Matrix.vecTail]

theorem tau_matrixUnit (i j : Fin 2) : (tau (K := K)).val (matrixUnit i j) = matrixUnit j i := by
  ext a b
  simp [tau_apply, matrixUnit, Matrix.single, and_comm]

theorem normalized_isometry_exhaustion (g : DeterminantIsometries K)
    (h1 : g.val 1 = 1) (he : g.val (matrixUnit 0 0) = matrixUnit 0 0) :
    ∃ c : Kˣ, g = rho (conjugationPair (diagonalUnit c)) ∨
      g = rho (conjugationPair (diagonalUnit c)) * tau := by
  obtain ⟨c, hc | hc⟩ := normalized_offdiagonal_dichotomy g h1 he
  · refine ⟨c, Or.inl (Subtype.ext (linearEquiv_ext_matrixUnit ?_))⟩
    intro i j
    rw [rho_diagonalUnit_matrixUnit]
    fin_cases i <;> fin_cases j
    · simpa using he
    · simpa using hc.1
    · simpa using hc.2
    · simpa using normalized_fixes_second_projector g h1 he
  · refine ⟨c, Or.inr (Subtype.ext (linearEquiv_ext_matrixUnit ?_))⟩
    intro i j
    change g.val (matrixUnit i j) =
      (rho (conjugationPair (diagonalUnit c))).val ((tau (K := K)).val (matrixUnit i j))
    rw [tau_matrixUnit, rho_diagonalUnit_matrixUnit]
    fin_cases i <;> fin_cases j
    · simpa using he
    · simpa using hc.1
    · simpa using hc.2
    · simpa using normalized_fixes_second_projector g h1 he

theorem determinant_isometry_exhaustion (g : DeterminantIsometries K) :
    ∃ z : equalDeterminants K, g = rho z ∨ g = rho z * tau := by
  obtain ⟨z, h, hg, h1, he⟩ := exists_normalized_isometry g
  obtain ⟨c, hc | hc⟩ := normalized_isometry_exhaustion h h1 he
  · refine ⟨z * conjugationPair (diagonalUnit c), Or.inl ?_⟩
    rw [hg, hc, map_mul]
  · refine ⟨z * conjugationPair (diagonalUnit c), Or.inr ?_⟩
    rw [hg, hc, map_mul, mul_assoc]

end CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
