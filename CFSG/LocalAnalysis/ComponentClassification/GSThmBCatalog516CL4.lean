module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CL4Graph
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphSymm
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphAlt

public section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4 InvClassL TBlocks HBlocks

variable {Y : Type} [Group Y] [Finite Y] {K : Type} [Field K] [Finite K] {p f : ℕ}

omit [Finite Y] in
theorem outer_of_normalForm (e : Y ⧸ center Y ≃* projectiveSL 4 K) (α : MulAut Y)
    {A : GL (Fin 4) K} {σ : K ≃+* K} {ε : ℕ} (hε : ε ≤ 1)
    (hα' : MulAut.congr e (barAut α) = conjAut 4 K A * fieldAut 4 K σ * dualAut 4 K ^ ε)
    (h : σ ≠ 1 ∨ ε = 1) : ∀ x, barAut α ≠ MulAut.conj x := by
  intro x hx
  obtain ⟨X, hX⟩ := OddSelector.exists_conjAut_of_mem_inner ((inner_iff_congr e α).mp ⟨x, hx⟩)
  rw [hα'] at hX
  obtain ⟨hσ, hε0, -⟩ := OddSelector.eq_of_conjAut_eq_normalForm (by norm_num) hε hX.symm
  rcases h with h | h
  · exact h hσ
  · omega

theorem concl_of_fixed_perfect (hZ : Nat.card (center Y) = 2)
    (e : Y ⧸ center Y ≃* projectiveSL 4 K) (α : MulAut Y) {β : MulAut (projectiveSL 4 K)}
    (hα' : MulAut.congr e (barAut α) = β) (hout : ∀ x, barAut α ≠ MulAut.conj x)
    {P : Subgroup (projectiveSL 4 K)} (hP : Group.IsPerfect P) (he : Even (Nat.card P))
    (hfix : ∀ s ∈ P, β s = s) (q : ℕ) : Concl516 Y α q := by
  set ρ := e.symm.toMonoidHom.comp P.subtype
  have hinj : Function.Injective ρ := e.symm.injective.comp P.subtype_injective
  have h4 : 4 ∣ Nat.card ρ.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact four_dvd_of_no_index_two (even_iff_two_dvd.mp he) no_index_two_of_perfect
  exact concl516_outer hZ α ρ (fun g => barAut_symm_fixed e α hα' (hfix g g.2)) (Or.inl hP)
    hout h4

variable (hZ : Nat.card (center Y) = 2) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
  (e : Y ⧸ center Y ≃* projectiveSL 4 K) (α : MulAut Y)

include hZ hp hp2 hK in
theorem cent516_conjAut [Group.IsPerfect Y] {A : GL (Fin 4) K}
    (hα' : MulAut.congr e (barAut α) = conjAut 4 K A) (h1 : barAut α ≠ 1)
    (hsq : conjAut 4 K A ^ 2 = 1) : Concl516 Y α (p ^ f) := by
  have hK2 := LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hK
  have hAA : conjAut 4 K (A * A) * fieldAut 4 K 1 = 1 := by
    rw [map_one, mul_one, map_mul, ← sq, hsq]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ hAA
  have hX : (A : Matrix (Fin 4) (Fin 4) K) * A = (c : K) • 1 := by
    rw [← Units.val_mul, ← hc, GeneralLinearGroup.coe_scalar, scalar_apply,
      smul_one_eq_diagonal]
  have hns : ∀ a : K, (A : Matrix (Fin 4) (Fin 4) K) ≠ a • 1 := by
    intro a ha
    apply h1
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      exact (Matrix.isUnits_det_units A).ne_zero (by rw [ha, det_zero])
    have hA : A = GeneralLinearGroup.scalar (Fin 4) (Units.mk0 a ha0) := by
      apply Units.ext
      rw [ha, GeneralLinearGroup.coe_scalar, scalar_apply, Units.val_mk0, smul_one_eq_diagonal]
    have : MulAut.congr e (barAut α) = 1 := by rw [hα', hA, conjAut_scalar]
    rw [← map_one (MulAut.congr e)] at this
    exact (MulAut.congr e).injective this
  rcases classify_inv hK2 hX (Units.ne_zero c) hns with
    ⟨l, hl0, -, -, P, hP⟩ | ⟨l, hl0, -, -, P, s, hs, hP⟩ | ⟨hnsq, P, hP⟩
  · refine diag_t2 hZ hp hp2 hK e α hα' (P := P) (μ := Units.mk0 l hl0) (Units.ext ?_)
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply,
      Units.val_mk0, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
    change (A : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      l • ((P : Matrix (Fin 4) (Fin 4) K) * X1 1)
    rw [← hP, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hl0, one_smul]
  · have hs0 : s * l⁻¹ ≠ 0 := mul_ne_zero (by rcases hs with rfl | rfl <;> norm_num)
      (inv_ne_zero hl0)
    refine diag_t1 hZ hp hp2 hK e α hα' (P := P) (μ := Units.mk0 (s * l⁻¹)⁻¹ (inv_ne_zero hs0))
      (Units.ext ?_)
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply,
      Units.val_mk0, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
    change (A : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      (s * l⁻¹)⁻¹ • ((P : Matrix (Fin 4) (Fin 4) K) * dOne)
    rw [← hP, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  · refine diag_N hZ hp hp2 hK e α hα' hnsq (Units.ne_zero c) (P := P) (Units.ext ?_)
    rw [Units.val_mul, Units.val_mul, map_one, Units.val_one, Matrix.one_mul]
    exact hP

include hZ hp hp2 hK e in
theorem cent516_linear_of_equiv [Group.IsPerfect Y] (hα : α ^ 2 = 1) :
    Concl516 Y α (p ^ f) := by
  have hK2 := LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hK
  by_cases h1 : barAut α = 1
  · exact concl516_one inferInstance α h1
  have hsq : MulAut.congr e (barAut α) ^ 2 = 1 := by
    rw [← map_pow, barAut_sq hα, map_one]
  obtain ⟨A, σ, ε, hε, hα'⟩ := (automorphism_generation (K := K) (by norm_num : 3 ≤ 4)).2
    (MulAut.congr e (barAut α))
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at hα'
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hα'
      exact cent516_conjAut hZ hp hp2 hK e α hα' h1 (hα' ▸ hsq)
    · have hout := outer_of_normalForm e α (A := A) (σ := σ) (ε := 0) (by norm_num)
        (by rw [pow_zero, mul_one]; exact hα') (Or.inl hσ)
      obtain ⟨P, hP, he, hfix⟩ := exists_fixed_perfect_even_conjAut_fieldAut hp (by
        rcases Nat.eq_zero_or_pos f with rfl | hf
        · rw [pow_zero] at hK
          exact absurd hK (Finite.one_lt_card).ne'
        · exact hf) hK (by norm_num) A σ hσ (hα' ▸ hsq)
      exact concl_of_fixed_perfect hZ e α hα' hout hP he hfix _
  · rw [pow_one] at hα'
    have hf1 : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | hf
      · rw [pow_zero] at hK
        exact absurd hK (Finite.one_lt_card).ne'
      · exact hf
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hα'
      have hout := outer_of_normalForm e α (A := A) (σ := 1) (ε := 1) le_rfl
        (by rw [map_one, mul_one, pow_one]; exact hα') (Or.inr rfl)
      rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut (by norm_num) A (hα' ▸ hsq) with
        hA | hA
      · by_cases h3 : p ^ f = 3
        · exact graph_sym3 hZ hp hp2 hK h3 e α hα' hA
        · obtain ⟨P, hP, he, hfix⟩ := exists_fixed_perfect_even_conjAut_dualAut_of_transpose_eq
            hK2 (exists_finset_four hp hp2 hK h3) (by norm_num) A hA
          exact concl_of_fixed_perfect hZ e α hα' hout hP he hfix _
      · by_cases h3 : p ^ f = 3
        · exact graph_alt3 hZ hp hp2 hK h3 e α hα' hA
        · obtain ⟨P, hP, he, hfix⟩ :=
            exists_fixed_perfect_even_conjAut_dualAut_of_transpose_eq_neg hK2
              (exists_finset_four hp hp2 hK h3) (by norm_num) A hA
          exact concl_of_fixed_perfect hZ e α hα' hout hP he hfix _
    · have hout := outer_of_normalForm e α (A := A) (σ := σ) (ε := 1) le_rfl
        (by rw [pow_one]; exact hα') (Or.inl hσ)
      obtain ⟨P, hP, he, hfix⟩ := exists_fixed_perfect_even_conjAut_fieldAut_dualAut hp hp2 hf1
        hK (by norm_num) A σ hσ (hα' ▸ hsq)
      exact concl_of_fixed_perfect hZ e α hα' hout hP he hfix _

theorem cent516_linear (hY : IsQuasisimple Y) (hZ : Nat.card (center Y) = 2) (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : Blueprint.LieModel (Y ⧸ center Y) .PSL 4 p f) (α : MulAut Y)
    (hα : α ^ 2 = 1) : Concl516 Y α (p ^ f) := by
  have := hY.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hm
  exact cent516_linear_of_equiv hZ hp hp2 hK e α hα

end CFSG.ComponentClassification.GSThmB.Cent516
