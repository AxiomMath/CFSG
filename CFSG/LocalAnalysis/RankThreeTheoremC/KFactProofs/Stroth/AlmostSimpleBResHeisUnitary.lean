module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem isPrimeFormGram_one_three {K : Type} [Field K] :
    IsPrimeFormGram (1 : GL (Fin 3) K) := by
  refine ⟨by rw [Units.val_one, transpose_one], fun i j => ?_⟩
  rw [Units.val_one, one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

private def hpairD {K : Type} [Field K] (ω : K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal ![1, ω, ω ^ 2]

private def hpairC (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 1, 0, 0; 0, 1, 0]

private theorem hpairD_pow_three {K : Type} [Field K] {ω : K} (hω3 : ω ^ 3 = 1) :
    hpairD ω ^ 3 = 1 := by
  rw [hpairD, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simp
  · simp [hω3]
  · simp
    linear_combination (ω ^ 3 + 1) * hω3

private theorem hpairC_pow_three (K : Type) [Field K] : hpairC K ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hpairC, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

private theorem hpairD_det {K : Type} [Field K] {ω : K} (hω3 : ω ^ 3 = 1) :
    (hpairD ω).det = 1 := by
  rw [hpairD, Matrix.det_diagonal, Fin.prod_univ_three]
  simp
  linear_combination hω3

private theorem hpairC_det (K : Type) [Field K] : (hpairC K).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [hpairC]

private theorem hpairD_unitary {f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData 2 f K) {ω : K}
    (hω3 : ω ^ 3 = 1) (hωb : hU.bar ω * ω = 1) (hbω2 : hU.bar (ω ^ 2) = ω) :
    ((hpairD ω).map hU.bar)ᵀ * hpairD ω = 1 := by
  rw [hpairD, Matrix.diagonal_map (map_zero hU.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simp
  · show hU.bar ω * ω = 1
    exact hωb
  · show hU.bar (ω ^ 2) * ω ^ 2 = 1
    rw [hbω2]
    linear_combination hω3

private theorem hpairC_unitary {f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData 2 f K) :
    ((hpairC K).map hU.bar)ᵀ * hpairC K = 1 := by
  have hm : (hpairC K).map hU.bar = hpairC K := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hpairC]
  rw [hm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hpairC, Matrix.mul_apply, Fin.sum_univ_three]

private theorem hpairC_mul_hpairD {K : Type} [Field K] {ω : K} (hω3 : ω ^ 3 = 1) :
    hpairC K * hpairD ω = hpairD ω * hpairC K * Matrix.scalar (Fin 3) (ω ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hpairC, hpairD, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply,
      Matrix.diagonal_apply]
  all_goals first
    | linear_combination hω3
    | linear_combination -hω3
    | linear_combination ω * hω3
    | linear_combination -(ω * hω3)

private theorem hpairD_map_of_fix {K : Type} [Field K] (τ : K ≃+* K) {ω : K} (hτω : τ ω = ω) :
    (hpairD ω).map τ = hpairD ω := by
  rw [hpairD, Matrix.diagonal_map (map_zero τ)]
  congr 1
  funext i
  fin_cases i <;> simp [hτω]

private theorem hpairC_map_of_fix {K : Type} [Field K] (τ : K ≃+* K) :
    (hpairC K).map τ = hpairC K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hpairC]

private theorem hpair_word_not_scalar {K : Type} [Field K] {ω : K} (hω0 : ω ≠ 0)
    (hω1 : ω ≠ 1) (hω2 : ω ^ 2 ≠ 1) {r s : ℕ} (hr : r < 3) (hs : s < 3) {c : K}
    (h : hpairD ω ^ r * hpairC K ^ s = Matrix.scalar (Fin 3) c) : r = 0 ∧ s = 0 := by
  interval_cases r <;> interval_cases s
  · exact ⟨rfl, rfl⟩
  · have e := congrFun (congrFun h 1) 0
    simp [hpairC, Matrix.scalar_apply, Matrix.diagonal_apply] at e
  · have e := congrFun (congrFun h 0) 1
    simp [pow_two, hpairC, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply,
      Matrix.diagonal_apply] at e
  · have e0 := congrFun (congrFun h 0) 0
    have e1 := congrFun (congrFun h 1) 1
    simp [hpairD, Matrix.scalar_apply, Matrix.diagonal_apply] at e0 e1
    exact absurd (by linear_combination e1 - e0 : ω = 1) hω1
  · have e := congrFun (congrFun h 1) 0
    simp [pow_two, hpairD, hpairC, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply,
      Matrix.diagonal_apply] at e
    exact absurd e hω0
  · have e := congrFun (congrFun h 0) 1
    simp [pow_two, hpairD, hpairC, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply,
      Matrix.diagonal_apply] at e
  · have e0 := congrFun (congrFun h 0) 0
    have e1 := congrFun (congrFun h 1) 1
    simp [pow_two, hpairD, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply,
      Matrix.diagonal_apply] at e0 e1
    exact absurd (by linear_combination e1 - e0 : ω ^ 2 = 1) hω2
  · have e := congrFun (congrFun h 0) 2
    simp [pow_two, hpairD, hpairC, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply,
      Matrix.diagonal_apply] at e
  · have e := congrFun (congrFun h 0) 1
    simp [pow_two, hpairD, hpairC, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply,
      Matrix.diagonal_apply] at e

private theorem hpair_word_GL {K : Type} [Field K] {ω : K} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    (hω2 : ω ^ 2 ≠ 1) {dG cG : GL (Fin 3) K} (hdG : (dG : Matrix (Fin 3) (Fin 3) K) = hpairD ω)
    (hcG : (cG : Matrix (Fin 3) (Fin 3) K) = hpairC K) {r s : ℕ} (hr : r < 3) (hs : s < 3)
    {c : Kˣ} (h : dG ^ r * cG ^ s = GeneralLinearGroup.scalar (Fin 3) c) :
    r = 0 ∧ s = 0 := by
  have hm := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, hdG, hcG,
    GeneralLinearGroup.coe_scalar] at hm
  exact hpair_word_not_scalar hω0 hω1 hω2 hr hs hm

private theorem zpow_eq_pow_emod_three {G : Type*} [Group G] (x : G) (hx : x ^ 3 = 1) (i : ℤ) :
    x ^ i = x ^ (i % 3).toNat := by
  have h3 : x ^ (3 : ℤ) = 1 := by simpa using hx
  rw [zpow_eq_zpow_emod i h3, ← zpow_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg i (by norm_num : (3 : ℤ) ≠ 0))]

theorem exists_heisenberg_pair_unitary {f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData 2 f K)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hωb : hU.bar ω * ω = 1) (τ : K ≃+* K) (hτω : τ ω = ω) :
    ∃ x₁ x₂ : primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      Commute x₁ x₂ ∧ x₁ ^ 3 = 1 ∧ x₂ ^ 3 = 1 ∧
      (∀ i j : ℤ, x₁ ^ i * x₂ ^ j = 1 → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j) ∧
      primeFormFieldHom hU (isPrimeFormGram_one_three (K := K)) τ x₁ = x₁ ∧
      primeFormFieldHom hU (isPrimeFormGram_one_three (K := K)) τ x₂ = x₂ := by
  haveI := hU.charP
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω + 1) * hω - (1 + ω + ω ^ 2) * h2
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hω1 : ω ≠ 1 := by
    rintro rfl
    have h10 : (1 : K) = 0 := by linear_combination hω - h2
    exact one_ne_zero h10
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    exact hω0 (by linear_combination hω - h - h2)
  have hbω : hU.bar ω = ω ^ 2 := by
    linear_combination ω ^ 2 * hωb - hU.bar ω * hω3
  have hbω2 : hU.bar (ω ^ 2) = ω := by
    rw [map_pow, hbω]
    linear_combination ω * hω3
  have hdetD : (hpairD ω).det ≠ 0 := by
    rw [hpairD_det hω3]
    exact one_ne_zero
  have hdetC : (hpairC K).det ≠ 0 := by
    rw [hpairC_det K]
    exact one_ne_zero
  obtain ⟨dG, hdG⟩ : ∃ g : GL (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K) = hpairD ω :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetD, rfl⟩
  obtain ⟨cG, hcG⟩ : ∃ g : GL (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K) = hpairC K :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetC, rfl⟩
  have hdS : dG ∈ gramSU hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [mem_gramSU, Units.val_one, Matrix.mul_one, hdG]
    exact ⟨hpairD_unitary hU hω3 hωb hbω2, hpairD_det hω3⟩
  have hcS : cG ∈ gramSU hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [mem_gramSU, Units.val_one, Matrix.mul_one, hcG]
    exact ⟨hpairC_unitary hU, hpairC_det K⟩
  obtain ⟨dS, hdSval⟩ : ∃ g : gramSU hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      (g : GL (Fin 3) K) = dG := ⟨⟨dG, hdS⟩, rfl⟩
  obtain ⟨cS, hcSval⟩ : ∃ g : gramSU hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      (g : GL (Fin 3) K) = cG := ⟨⟨cG, hcS⟩, rfl⟩
  have hdG3 : dG ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hdG, Units.val_one]
    exact hpairD_pow_three hω3
  have hcG3 : cG ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hcG, Units.val_one]
    exact hpairC_pow_three K
  have hdS3 : dS ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hdSval, Subgroup.coe_one]
    exact hdG3
  have hcS3 : cS ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hcSval, Subgroup.coe_one]
    exact hcG3
  obtain ⟨u, huval⟩ : ∃ u : Kˣ, (u : K) = ω ^ 2 := ⟨Units.mk0 _ (pow_ne_zero 2 hω0), rfl⟩
  have hun : hU.norm (u : K) = 1 := by
    rw [huval, UnitaryFieldData.norm, hbω2]
    linear_combination hω3
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, huval]
    linear_combination (ω ^ 3 + 1) * hω3
  have hscal : GeneralLinearGroup.scalar (Fin 3) u ∈
      gramSU hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [Units.val_one, ← unitarySU_eq_gramSU hU 3]
    exact scalar_mem_unitarySU hU (by norm_num) hun hu3
  have hrel : cG * dG = dG * cG * GeneralLinearGroup.scalar (Fin 3) u := by
    apply Units.ext
    simp only [Units.val_mul, hdG, hcG, GeneralLinearGroup.coe_scalar, huval]
    exact hpairC_mul_hpairD hω3
  have hcomm : (dS * cS)⁻¹ * (cS * dS) = ⟨GeneralLinearGroup.scalar (Fin 3) u, hscal⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hdSval, hcSval]
    rw [hrel, inv_mul_cancel_left]
  have hzN : (⟨GeneralLinearGroup.scalar (Fin 3) u, hscal⟩ : gramSU hU
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ∈
      normOneScalars hU (gramSU hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3 :=
    mem_normOneScalars.2 ⟨u, hun, hu3, rfl⟩
  refine ⟨QuotientGroup.mk dS, QuotientGroup.mk cS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [Commute, SemiconjBy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      hcomm]
    exact hzN
  · rw [← QuotientGroup.mk_pow, hdS3, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_pow, hcS3, QuotientGroup.mk_one]
  ·
    intro i j hij
    rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul,
      QuotientGroup.eq_one_iff] at hij
    obtain ⟨v, -, -, hv⟩ := mem_normOneScalars.1 hij
    have hv' : dG ^ i * cG ^ j = GeneralLinearGroup.scalar (Fin 3) v := by
      rw [← hdSval, ← hcSval]
      simpa using hv
    rw [zpow_eq_pow_emod_three dG hdG3 i, zpow_eq_pow_emod_three cG hcG3 j] at hv'
    obtain ⟨h1, h2'⟩ := hpair_word_GL hω0 hω1 hω2 hdG hcG (by omega) (by omega) hv'
    exact ⟨by omega, by omega⟩
  ·
    have hfix : primeFormFieldSU hU (isPrimeFormGram_one_three (K := K)) τ dS = dS := by
      apply Subtype.ext
      show glAut τ (dS : GL (Fin 3) K) = (dS : GL (Fin 3) K)
      rw [hdSval]
      apply Units.ext
      rw [coe_glAut, hdG, hpairD_map_of_fix τ hτω]
    show primeFormFieldAut hU (isPrimeFormGram_one_three (K := K)) τ (QuotientGroup.mk dS) =
      QuotientGroup.mk dS
    rw [primeFormFieldAut_mk hU (isPrimeFormGram_one_three (K := K)) τ dS, hfix]
  ·
    have hfix : primeFormFieldSU hU (isPrimeFormGram_one_three (K := K)) τ cS = cS := by
      apply Subtype.ext
      show glAut τ (cS : GL (Fin 3) K) = (cS : GL (Fin 3) K)
      rw [hcSval]
      apply Units.ext
      rw [coe_glAut, hcG, hpairC_map_of_fix τ]
    show primeFormFieldAut hU (isPrimeFormGram_one_three (K := K)) τ (QuotientGroup.mk cS) =
      QuotientGroup.mk cS
    rw [primeFormFieldAut_mk hU (isPrimeFormGram_one_three (K := K)) τ cS, hfix]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
