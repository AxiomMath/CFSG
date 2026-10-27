module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearConjugacy
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedSpan
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2

public section

namespace CFSG.ClassicalInvolution

open scoped MatrixGroups

open Matrix CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBLinearSemilinear

private theorem exists_binary_form {F : Type*} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (t : F) : ∃ x y : F, u * x ^ 2 + v * y ^ 2 = t := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let f : Polynomial F := Polynomial.C u * Polynomial.X ^ 2
  let g : Polynomial F := Polynomial.C v * Polynomial.X ^ 2 - Polynomial.C t
  have hf : f.degree = 2 := by simpa [f] using Polynomial.degree_C_mul_X_pow 2 hu
  have hg : g.degree = 2 := by
    have h2 : (Polynomial.C v * Polynomial.X ^ 2).degree = 2 := by
      simpa using Polynomial.degree_C_mul_X_pow 2 hv
    have : 0 < (Polynomial.C v * Polynomial.X ^ 2).degree := by rw [h2]; norm_num
    simpa [g, h2] using Polynomial.degree_sub_C this
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg
    (Nat.odd_iff.mp (by simpa only [Nat.card_eq_fintype_card] using hodd))
  refine ⟨a, b, ?_⟩
  simp only [f, g, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub] at hab
  linear_combination hab

private theorem exists_anticommuting_aux {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (a b e : F) (hb : b ≠ 0) (hc : a ^ 2 + b * e ≠ 0) :
    ∃ p r s : F, 2 * a * p + b * s + e * r = 0 ∧ p ^ 2 + r * s = -1 := by
  obtain ⟨x, y, hxy⟩ := exists_binary_form hodd hb (v := -(a ^ 2 + b * e) / b)
    (div_ne_zero (neg_ne_zero.mpr hc) hb) (-b)
  refine ⟨x + a / b * y, y, -(2 * a * (x + a / b * y) + e * y) / b, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    field_simp at hxy
    linear_combination hxy

private theorem exists_anticommuting_explicit {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (a b e : F) (hc : a ^ 2 + b * e ≠ 0) :
    ∃ w : SL(2, F), (!![a, b; e, -a] : Matrix (Fin 2) (Fin 2) F) *
        (w : Matrix (Fin 2) (Fin 2) F) =
      -((w : Matrix (Fin 2) (Fin 2) F) * !![a, b; e, -a]) := by
  have key : ∀ p r s : F, 2 * a * p + b * s + e * r = 0 → p ^ 2 + r * s = -1 →
      ∃ w : SL(2, F), (!![a, b; e, -a] : Matrix (Fin 2) (Fin 2) F) *
        (w : Matrix (Fin 2) (Fin 2) F) =
        -((w : Matrix (Fin 2) (Fin 2) F) * !![a, b; e, -a]) := by
    intro p r s hlin hdet
    refine ⟨⟨!![p, r; s, -p], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of]
      linear_combination -hdet
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination hlin
      · ring
      · ring
      · linear_combination hlin
  by_cases hb : b = 0
  · by_cases he : e = 0
    · have ha : a ≠ 0 := by
        intro ha
        apply hc
        rw [ha, hb]
        ring
      apply key 0 1 (-1)
      · rw [hb, he]
        ring
      · ring
    · obtain ⟨p, s', r', hlin, hdet⟩ := exists_anticommuting_aux hodd a e b he
        (by intro h; apply hc; linear_combination h)
      exact key p r' s' (by linear_combination hlin) (by linear_combination hdet)
  · obtain ⟨p, r, s, hlin, hdet⟩ := exists_anticommuting_aux hodd a b e hb hc
    exact key p r s hlin hdet

private theorem exists_anticommuting {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (A : Matrix (Fin 2) (Fin 2) F) (c : F) (hc : c ≠ 0)
    (hsq : A * A = Matrix.scalar (Fin 2) c) (hns : ∀ k : F, A ≠ Matrix.scalar (Fin 2) k) :
    ∃ w : SL(2, F), A * (w : Matrix (Fin 2) (Fin 2) F) =
      -((w : Matrix (Fin 2) (Fin 2) F) * A) := by
  have h00 : A 0 0 * A 0 0 + A 0 1 * A 1 0 = c := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hsq 0) 0
  have h01 : A 0 0 * A 0 1 + A 0 1 * A 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hsq 0) 1
  have h10 : A 1 0 * A 0 0 + A 1 1 * A 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hsq 1) 0
  have h11 : A 1 0 * A 0 1 + A 1 1 * A 1 1 = c := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hsq 1) 1
  have htr : A 1 1 = -A 0 0 := by
    by_contra hne
    have hsum : A 0 0 + A 1 1 ≠ 0 := by
      intro h
      apply hne
      linear_combination h
    have hb : A 0 1 = 0 := by
      have : A 0 1 * (A 0 0 + A 1 1) = 0 := by linear_combination h01
      exact (mul_eq_zero.mp this).resolve_right hsum
    have he : A 1 0 = 0 := by
      have : A 1 0 * (A 0 0 + A 1 1) = 0 := by linear_combination h10
      exact (mul_eq_zero.mp this).resolve_right hsum
    have hdiag : A 0 0 = A 1 1 := by
      have : (A 0 0 - A 1 1) * (A 0 0 + A 1 1) = 0 := by
        rw [hb, he] at h00 h11
        linear_combination h00 - h11
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hsum)
    apply hns (A 0 0)
    rw [Matrix.eta_fin_two A, hb, he, ← hdiag]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hA : A = !![A 0 0, A 0 1; A 1 0, -A 0 0] := by
    rw [← htr]
    exact Matrix.eta_fin_two A
  rw [hA]
  apply exists_anticommuting_explicit hodd
  intro h
  apply hc
  rw [← h00]
  linear_combination h

private theorem centerQuotientHom_slConjugation {F : Type*} [Field F] (H : GL (Fin 2) F) :
    centerQuotientHom SL(2, F) (slConjugation 2 F H) = innerDiagonalAction 2 F H := by
  apply MulEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, F)) x
  exact (onCenterQuotient_apply_mk _ g).trans (innerDiagonalAction_mk 2 F H g).symm

private theorem centerQuotientHom_slFieldAut {F : Type*} [Field F] (σ : F ≃+* F) :
    centerQuotientHom SL(2, F) (slFieldAut (Fin 2) F σ) = pslFieldAut (Fin 2) F σ := by
  apply MulEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, F)) x
  exact (onCenterQuotient_apply_mk _ g).trans (pslFieldAut_mk (Fin 2) F σ g).symm

private theorem schreier_pglAction_eq {F : Type*} [Field F]
    (g : Matrix.ProjGenLinGroup (Fin 2) F) :
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction F g =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.pglAction 2 F g := by
  ext x
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [CFSG.ComponentClassification.CatalogueSchreierLinearTwo.toPGL_pglAction,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.toPGL_pglAction]

private theorem exists_slConjugation_mul_slFieldAut {F : Type*} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) (α : MulAut SL(2, F)) :
    ∃ (A : GL (Fin 2) F) (σ : F ≃+* F), α = slConjugation 2 F A * slFieldAut (Fin 2) F σ := by
  have hperf : Group.IsPerfect SL(2, F) := specialLinear_perfect 2 F le_rfl (Or.inr h4)
  obtain ⟨x, hx⟩ :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_surjective F
      (centerQuotientHom SL(2, F) α)
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective x.left
  refine ⟨A, x.right, centerQuotientHom_injective SL(2, F) ?_⟩
  have hx' : CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction F x =
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction F x.left *
        CFSG.GorensteinWalter.psl2FieldAut F x.right := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
    rw [map_mul, CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inl,
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inr]
  rw [map_mul, centerQuotientHom_slConjugation, centerQuotientHom_slFieldAut, ← hx, hx',
    schreier_pglAction_eq, ← hA, pslFieldAut_two]
  rfl

private theorem centerQuotientHom_slSemilinear {F : Type*} [Field F] (A : GL (Fin 2) F)
    (σ : F ≃+* F) :
    centerQuotientHom SL(2, F) (slConjugation 2 F A * slFieldAut (Fin 2) F σ) =
      semilinearAction 2 F A σ := by
  rw [map_mul, centerQuotientHom_slConjugation, centerQuotientHom_slFieldAut]
  rfl

private theorem sl_eq_of_coe_eq {F : Type*} [Field F] {v w : SL(2, F)}
    (h : (v : Matrix (Fin 2) (Fin 2) F) = (w : Matrix (Fin 2) (Fin 2) F)) : v = w :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => congrFun (congrFun h i) j

private theorem coe_mul_neg_one {F : Type*} [Field F] (w : SL(2, F)) :
    ((w * (-1) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -(w : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, mul_neg, mul_one]

private theorem exists_w_of_conj_fieldAut {F : Type*} [Field F] (H : GL (Fin 2) F)
    (σ : F ≃+* F) (δ : F) (hδ0 : δ ≠ 0) (hδ : σ δ = -δ) :
    ∃ w : SL(2, F),
      (slConjugation 2 F H * slFieldAut (Fin 2) F σ * (slConjugation 2 F H)⁻¹) w = w * (-1) := by
  let w₀ : SL(2, F) := ⟨!![δ, 0; 0, δ⁻¹], by simp [Matrix.det_fin_two_of, hδ0]⟩
  have hw₀ : slFieldAut (Fin 2) F σ w₀ = w₀ * (-1) := by
    apply sl_eq_of_coe_eq
    rw [coe_mul_neg_one]
    ext i j
    change σ ((w₀ : Matrix (Fin 2) (Fin 2) F) i j) = _
    fin_cases i <;> fin_cases j <;> simp [w₀, hδ, map_inv₀]
  have hneg : slConjugation 2 F H (-1) = -1 := by
    apply sl_eq_of_coe_eq
    rw [slConjugation_matrix, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      mul_neg, mul_one, neg_mul, Units.mul_inv]
  refine ⟨slConjugation 2 F H w₀, ?_⟩
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hw₀,
    map_mul, hneg]

private theorem w_lemma_field_ne_one {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    (α : MulAut SL(2, F)) (hα : α * α = 1) (A : GL (Fin 2) F) (σ : F ≃+* F)
    (hασ : α = slConjugation 2 F A * slFieldAut (Fin 2) F σ) (hσ : σ ≠ 1) :
    ∃ w : SL(2, F), α w = w * (-1) := by
  have hperf : Group.IsPerfect SL(2, F) := specialLinear_perfect 2 F le_rfl (Or.inr h4)
  have htwo : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hsq : semilinearAction 2 F A σ ^ 2 = 1 := by
    rw [← centerQuotientHom_slSemilinear, ← hασ, ← map_pow, pow_two, hα, map_one]
  obtain ⟨hσ2, H, hH⟩ := field_involution_conjugacy 2 F le_rfl (Or.inr h4) htwo A σ hσ hsq
  have hα' : α = slConjugation 2 F H * slFieldAut (Fin 2) F σ * (slConjugation 2 F H)⁻¹ := by
    apply centerQuotientHom_injective SL(2, F)
    rw [map_mul, map_mul, map_inv, centerQuotientHom_slConjugation,
      centerQuotientHom_slFieldAut, ← hH, hασ, centerQuotientHom_slSemilinear]
  obtain ⟨δ, hδ0, hδ⟩ :=
    CFSG.ComponentClassification.CatalogueBLinearDescent.exists_antifixed_coefficient σ hσ2 hσ
  rw [hα']
  exact exists_w_of_conj_fieldAut H σ δ hδ0 hδ

private theorem w_lemma_field_eq_one {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    (α : MulAut SL(2, F)) (hα : α * α = 1) (hne : α ≠ 1) (A : GL (Fin 2) F)
    (hασ : α = slConjugation 2 F A * slFieldAut (Fin 2) F 1) :
    ∃ w : SL(2, F), α w = w * (-1) := by
  have hα' : α = slConjugation 2 F A := by rw [hασ, map_one, mul_one]
  have hsq : semilinearAction 2 F A 1 ^ 2 = 1 := by
    rw [← centerQuotientHom_slSemilinear, ← hασ, ← map_pow, pow_two, hα, map_one]
  obtain ⟨-, c, hc⟩ := involution_scalar_cocycle 2 F le_rfl (Or.inr h4) A 1 hsq
  have hAA : A.val * A.val = Matrix.scalar (Fin 2) (c : F) := by
    have := congrArg Units.val hc
    simpa using this.symm
  have hns : ∀ k : F, A.val ≠ Matrix.scalar (Fin 2) k := by
    intro k hk
    apply hne
    have hcenter : A ∈ Subgroup.center (GL (Fin 2) F) :=
      GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨k, hk.symm⟩
    rw [GeneralLinearGroup.center_eq_range_scalar] at hcenter
    obtain ⟨u, rfl⟩ := hcenter
    rw [hα', slConjugation_scalar]
  obtain ⟨w, hw⟩ := exists_anticommuting hodd A.val (c : F) c.ne_zero hAA hns
  refine ⟨w, ?_⟩
  rw [hα']
  have key : ((slConjugation 2 F A w : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      ((w * (-1) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    rw [slConjugation_matrix, coe_mul_neg_one, hw, neg_mul, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  exact sl_eq_of_coe_eq key

theorem w_lemma {F : Type*} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (α : MulAut SL(2, F)) (hα : α * α = 1) (hne : α ≠ 1) :
    ∃ w : SL(2, F), α w = w * (-1) := by
  obtain ⟨A, σ, hασ⟩ := exists_slConjugation_mul_slFieldAut (by omega) α
  by_cases hσ : σ = 1
  · subst hσ
    exact w_lemma_field_eq_one hodd (by omega) α hα hne A hασ
  · exact w_lemma_field_ne_one hodd (by omega) α hα A σ hασ hσ

end CFSG.ClassicalInvolution
