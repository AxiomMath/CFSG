module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldPSL
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.IVK Matrix
open scoped commutatorElement

theorem l3bf_eq_of_perfect {Γ G : Type*} [Group Γ] [Group G] (hΓ : commutator Γ = ⊤)
    (φ₁ φ₂ : Γ →* G) (h : ∀ g, (φ₂ g)⁻¹ * φ₁ g ∈ Subgroup.center G) : φ₁ = φ₂ := by
  have hle : commutator Γ ≤ φ₁.eqLocus φ₂ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have ha : φ₁ a = φ₂ a * ((φ₂ a)⁻¹ * φ₁ a) := by group
    have hb : φ₁ b = φ₂ b * ((φ₂ b)⁻¹ * φ₁ b) := by group
    show φ₁ ⁅a, b⁆ = φ₂ ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement, ha, hb,
      l3bf_commutator_central_mul (h a) (h b)]
  rw [hΓ] at hle
  ext g
  exact hle (Subgroup.mem_top g)

section Transvection

variable {R S : Type*} [CommRing R] [CommRing S]

theorem l3bf_map_transvection (f : R →+* S) {i j : Fin 3} (hij : i ≠ j) (c : R) :
    SpecialLinearGroup.map f (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection hij (f c) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe]
  ext a b
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp [hij]
  · by_cases hab : a = b
    · subst hab
      have : ¬ (i = a ∧ j = a) := fun ⟨h1, h2⟩ => hij (h1.trans h2.symm)
      simp [this]
    · simp [h, hab]

theorem l3bf_transvection_mul_neg (c : R) {i j : Fin 3} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij c * SpecialLinearGroup.transvection hij (-c) = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe]
  have : (Matrix.single i j c : Matrix (Fin 3) (Fin 3) R) * Matrix.single i j (-c) = 0 := by
    simp [hij.symm]
  have h2 : (Matrix.single i j (-c) : Matrix (Fin 3) (Fin 3) R) + Matrix.single i j c = 0 := by
    rw [← Matrix.single_add, neg_add_cancel, Matrix.single_zero]
  rw [add_mul, mul_add, mul_add, this]
  simp only [mul_one, one_mul, add_zero]
  rw [add_assoc, h2, add_zero]
  rfl

theorem l3bf_slGraphAut_transvection {R : Type} [Field R] (c : R) {i j : Fin 3} (hij : i ≠ j) :
    ((CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 R
      (SpecialLinearGroup.transvection hij c) : SpecialLinearGroup (Fin 3) R) :
        Matrix (Fin 3) (Fin 3) R) = 1 + Matrix.single j i (-c) := by
  have hinv : (SpecialLinearGroup.transvection hij c)⁻¹ = SpecialLinearGroup.transvection hij (-c) :=
    inv_eq_of_mul_eq_one_right (l3bf_transvection_mul_neg c hij)
  calc ((CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 R
        (SpecialLinearGroup.transvection hij c) : SpecialLinearGroup (Fin 3) R) :
          Matrix (Fin 3) (Fin 3) R)
      = (((SpecialLinearGroup.transvection hij c)⁻¹ : SpecialLinearGroup (Fin 3) R) :
          Matrix (Fin 3) (Fin 3) R).transpose :=
        CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix 3 R _
    _ = (((SpecialLinearGroup.transvection hij (-c) : SpecialLinearGroup (Fin 3) R)) :
          Matrix (Fin 3) (Fin 3) R).transpose := by rw [hinv]
    _ = 1 + Matrix.single j i (-c) := by
        rw [SpecialLinearGroup.transvection_coe, Matrix.transpose_add, Matrix.transpose_one,
          Matrix.transpose_single]

end Transvection

theorem l3bf_mem_zpowers_of_fixes {F : Type} [Field F] [Finite F] (σ τ : F ≃+* F)
    (hτ : ∀ t : F, σ t = t → τ t = t) : τ ∈ Subgroup.zpowers σ := by
  classical
  have hG : IsGaloisGroup (Subgroup.zpowers σ) (fixedField σ) F :=
    IsGaloisGroup.fixedPoints (Subgroup.zpowers σ) F
  let τ' : F ≃ₐ[fixedField σ] F := AlgEquiv.ofRingEquiv (f := τ) (fun x => by
    exact hτ x ((mem_fixedField_iff σ x).mp x.2))
  obtain ⟨h, hh⟩ :=
    (IsGaloisGroup.mulEquivAlgEquiv (Subgroup.zpowers σ) (fixedField σ) F).surjective τ'
  have hτh : (h : F ≃+* F) = τ := by
    ext x
    have := congrArg (fun a : F ≃ₐ[fixedField σ] F => a x) hh
    exact this
  rw [← hτh]
  exact h.2

section Rigid

variable {F : Type} [Field F] (σ : F ≃+* F)

@[expose] noncomputable def l3bI : SpecialLinearGroup (Fin 3) (fixedField σ) →*
    SpecialLinearGroup (Fin 3) F :=
  SpecialLinearGroup.map (n := Fin 3) (fixedField σ).subtype

theorem l3bI_transvection {i j : Fin 3} (hij : i ≠ j) (c : fixedField σ) :
    l3bI σ (SpecialLinearGroup.transvection hij c) = SpecialLinearGroup.transvection hij (c : F) :=
  l3bf_map_transvection (fixedField σ).subtype hij c

theorem l3bf_perfect_sl3 :
    commutator (SpecialLinearGroup (Fin 3) (fixedField σ)) = ⊤ :=
  (Group.isPerfect_def (G := SpecialLinearGroup (Fin 3) (fixedField σ))).1
    (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl)

theorem l3bf_comm_of_conj {A Ai X : Matrix (Fin 3) (Fin 3) F} (h1 : Ai * A = 1)
    (h : A * (1 + X) * Ai = 1 + X) : A * X = X * A := by
  have h2 := congrArg (fun Y => Y * A) h
  simp only [mul_assoc, h1, mul_one] at h2
  rw [mul_add, add_mul, mul_one, one_mul] at h2
  exact add_left_cancel h2

theorem l3bf_eq_of_fixes
    {φ₂ : SpecialLinearGroup (Fin 3) (fixedField σ) →* SpecialLinearGroup (Fin 3) F}
    (hφ : ∀ g, proj 3 F (φ₂ g) = proj 3 F (l3bI σ g)) : φ₂ = l3bI σ := by
  apply l3bf_eq_of_perfect (l3bf_perfect_sl3 σ)
  intro g
  have := proj_eq_proj_iff.1 (hφ g).symm
  rw [← scalars_eq_center]
  exact this

open CFSG.ComponentClassification in
theorem l3bf_rigid_psl_zero [Finite F] (ρ : MulAut (projectiveSL 3 F))
    (hρ : ∀ g, ρ (l3bG σ g) = l3bG σ g) (A : GL (Fin 3) F) (τ : F ≃+* F)
    (hρe : ρ = conjAut 3 F A * fieldAut 3 F τ) : ρ ∈ Subgroup.zpowers (fieldAut 3 F σ) := by
  let φ₁ : SpecialLinearGroup (Fin 3) (fixedField σ) →* SpecialLinearGroup (Fin 3) F :=
    ((CatalogueBHigherLinearAction.slConjugation 3 F A : MulAut _) :
      SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F).comp
      ((SpecialLinearGroup.map τ.toRingHom).comp (l3bI σ))
  have hφ : ∀ g, proj 3 F (φ₁ g) = proj 3 F (l3bI σ g) := by
    intro g
    have h := hρ g
    rw [hρe] at h
    change (conjAut 3 F A * fieldAut 3 F τ) (proj 3 F (l3bI σ g)) = proj 3 F (l3bI σ g) at h
    rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj] at h
    exact h
  have heq := l3bf_eq_of_fixes σ hφ
  have hg : ∀ {i j : Fin 3} (hij : i ≠ j) (c : fixedField σ),
      A.val * (1 + Matrix.single i j (τ (c : F))) * (A⁻¹).val = 1 + Matrix.single i j (c : F) := by
    intro i j hij c
    have h := congrArg (fun φ => ((φ (SpecialLinearGroup.transvection hij c) :
      SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) heq
    simp only [φ₁, MonoidHom.comp_apply, l3bI_transvection] at h
    rw [l3bf_map_transvection τ.toRingHom] at h
    change (CatalogueBHigherLinearAction.slConjugation 3 F A
      (SpecialLinearGroup.transvection hij (τ (c : F))) : Matrix (Fin 3) (Fin 3) F) = _ at h
    rw [CatalogueBHigherLinearAction.slConjugation_matrix, SpecialLinearGroup.transvection_coe,
      SpecialLinearGroup.transvection_coe] at h
    exact h
  have hcomm : ∀ {i j : Fin 3}, i ≠ j → A.val * Matrix.single i j 1 = Matrix.single i j 1 * A.val := by
    intro i j hij
    have h := hg hij 1
    simp only [OneMemClass.coe_one, map_one] at h
    exact l3bf_comm_of_conj (Units.inv_mul A) h
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_single
    (M := A.val) (fun i j hij => (hcomm hij).symm)
  have hconj : ∀ Y : Matrix (Fin 3) (Fin 3) F, A.val * Y * (A⁻¹).val = Y := by
    intro Y
    calc A.val * Y * (A⁻¹).val = Y * A.val * (A⁻¹).val := by
          rw [← hr, (Matrix.scalar_commute r (fun _ => Commute.all _ _) Y).eq]
      _ = Y := by rw [mul_assoc, Units.mul_inv, mul_one]
  have hτ : ∀ t : F, σ t = t → τ t = t := by
    intro t ht
    have h := hg (i := 0) (j := 1) (by decide) ⟨t, (mem_fixedField_iff σ t).2 ht⟩
    rw [hconj] at h
    have h2 := congrFun (congrFun h 0) 1
    simpa using h2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (l3bf_mem_zpowers_of_fixes σ τ hτ)
  have hc1 : conjAut 3 F A = 1 := by
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective 3 F x
    rw [conjAut_proj]
    have : CatalogueBHigherLinearAction.slConjugation 3 F A g = g := by
      apply Subtype.ext
      rw [CatalogueBHigherLinearAction.slConjugation_matrix, hconj]
    rw [this]
    rfl
  rw [hρe, hc1, one_mul, ← hk, map_zpow]
  exact Subgroup.zpow_mem_zpowers _ _

theorem l3bf_map_one_add_single (f : F →+* F) (i j : Fin 3) (a : F) :
    (1 + Matrix.single i j a : Matrix (Fin 3) (Fin 3) F).map f = 1 + Matrix.single i j (f a) := by
  ext x y
  simp only [Matrix.map_apply, Matrix.add_apply, map_add]
  congr 1
  · by_cases hxy : x = y <;> simp [Matrix.one_apply, hxy]
  · by_cases h : i = x ∧ j = y
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · simp [h]

open CFSG.ComponentClassification in
theorem l3bf_rigid_psl_one [Finite F] (ρ : MulAut (projectiveSL 3 F))
    (hρ : ∀ g, ρ (l3bG σ g) = l3bG σ g) (A : GL (Fin 3) F) (τ : F ≃+* F)
    (hρe : ρ = conjAut 3 F A * fieldAut 3 F τ * dualAut 3 F) : False := by
  let φ₂ : SpecialLinearGroup (Fin 3) (fixedField σ) →* SpecialLinearGroup (Fin 3) F :=
    ((CatalogueBHigherLinearAction.slConjugation 3 F A : MulAut _) :
      SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F).comp
      ((SpecialLinearGroup.map τ.toRingHom).comp
        (((CatalogueBGraphForm.slGraphAut 3 F : MulAut _) :
          SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F).comp (l3bI σ)))
  have hφ : ∀ g, proj 3 F (φ₂ g) = proj 3 F (l3bI σ g) := by
    intro g
    have h := hρ g
    rw [hρe] at h
    change (conjAut 3 F A * fieldAut 3 F τ * dualAut 3 F) (proj 3 F (l3bI σ g)) =
      proj 3 F (l3bI σ g) at h
    rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj] at h
    exact h
  have heq := l3bf_eq_of_fixes σ hφ
  have hg : ∀ {i j : Fin 3} (hij : i ≠ j),
      A.val * (1 + Matrix.single j i (-1)) * (A⁻¹).val = 1 + Matrix.single i j 1 := by
    intro i j hij
    have h := congrArg (fun φ => ((φ (SpecialLinearGroup.transvection hij (1 : fixedField σ)) :
      SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) heq
    simp only [φ₂, MonoidHom.comp_apply, l3bI_transvection] at h
    change (CatalogueBHigherLinearAction.slConjugation 3 F A
      ((SpecialLinearGroup.map τ.toRingHom)
        (CatalogueBGraphForm.slGraphAut 3 F (SpecialLinearGroup.transvection hij ((1 : fixedField σ) : F))))
        : Matrix (Fin 3) (Fin 3) F) = _ at h
    rw [CatalogueBHigherLinearAction.slConjugation_matrix, SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, l3bf_slGraphAut_transvection, l3bf_map_one_add_single,
      SpecialLinearGroup.transvection_coe] at h
    simpa using h
  have hrel : ∀ {i j : Fin 3}, i ≠ j →
      A.val * Matrix.single j i 1 * (A⁻¹).val = -Matrix.single i j 1 := by
    intro i j hij
    have h := hg hij
    rw [mul_add, add_mul, mul_one, Units.mul_inv] at h
    have h2 : A.val * Matrix.single j i (-1) * (A⁻¹).val = Matrix.single i j 1 := by
      have := add_left_cancel h
      exact this
    rw [← Matrix.single_neg, Matrix.mul_neg, Matrix.neg_mul] at h2
    exact neg_eq_iff_eq_neg.1 h2
  have h01 := hrel (i := 0) (j := 1) (by decide)
  have h12 := hrel (i := 1) (j := 2) (by decide)
  have h02 := hrel (i := 0) (j := 2) (by decide)
  have hprod : (Matrix.single (2 : Fin 3) (0 : Fin 3) (1 : F) : Matrix (Fin 3) (Fin 3) F) =
      (Matrix.single (2 : Fin 3) (1 : Fin 3) (1 : F) : Matrix (Fin 3) (Fin 3) F) *
        (Matrix.single (1 : Fin 3) (0 : Fin 3) (1 : F) : Matrix (Fin 3) (Fin 3) F) := by
    have := Matrix.single_mul_single_same (c := (1 : F)) (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (1 : F)
    rw [this, mul_one]
  have h3 : A.val * (Matrix.single (2 : Fin 3) (0 : Fin 3) (1 : F) : Matrix (Fin 3) (Fin 3) F) *
        (A⁻¹).val =
      (A.val * (Matrix.single (2 : Fin 3) (1 : Fin 3) (1 : F) : Matrix (Fin 3) (Fin 3) F) *
        (A⁻¹).val) *
      (A.val * (Matrix.single (1 : Fin 3) (0 : Fin 3) (1 : F) : Matrix (Fin 3) (Fin 3) F) *
        (A⁻¹).val) := by
    rw [hprod]
    simp only [mul_assoc]
    rw [← mul_assoc (A⁻¹).val, Units.inv_mul, one_mul]
  rw [h02, h12, h01, Matrix.neg_mul, Matrix.mul_neg, neg_neg] at h3
  have h5 : (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : F) : Matrix (Fin 3) (Fin 3) F) *
      (Matrix.single (0 : Fin 3) (1 : Fin 3) (1 : F) : Matrix (Fin 3) (Fin 3) F) = 0 := by simp
  rw [h5] at h3
  have h4 := congrFun (congrFun h3 0) 2
  simp at h4

theorem l3bf_rigid_psl [Finite F] (ρ : MulAut (projectiveSL 3 F))
    (hρ : ∀ g, ρ (l3bG σ g) = l3bG σ g) : ρ ∈ Subgroup.zpowers (fieldAut 3 F σ) := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 3) (by norm_num)
  obtain ⟨A, τ, ε, hε, h⟩ := hgen ρ
  interval_cases ε
  · exact l3bf_rigid_psl_zero σ ρ hρ A τ (by simpa using h)
  · exact (l3bf_rigid_psl_one σ ρ hρ A τ (by simpa using h)).elim

end Rigid

end CFSG.HardMathSupport.Solomon.Coordinator
