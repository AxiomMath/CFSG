module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PLd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpOrth

public section

namespace CFSG.ComponentClassification.GSThmB.P211

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4 InvClassL

variable {F : Type} [Field F]

@[expose] noncomputable def graphLift (A : GL (Fin 4) F) : MulAut (SpecialLinearGroup (Fin 4) F) :=
  CatalogueBHigherLinearAction.slConjugation 4 F A * CatalogueBGraphForm.slGraphAut 4 F

theorem graphLift_proj (A : GL (Fin 4) F) (g : SpecialLinearGroup (Fin 4) F) :
    (conjAut 4 F A * dualAut 4 F) (proj 4 F g) = proj 4 F (graphLift A g) := by
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj]
  rfl

theorem coe_graphLift (A : GL (Fin 4) F) (g : SpecialLinearGroup (Fin 4) F) :
    ((graphLift A g : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (A : Matrix (Fin 4) (Fin 4) F) *
        ((g⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
          ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  change ((CatalogueBHigherLinearAction.slConjugation 4 F A ((g⁻¹).transpose) :
    SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = _
  rw [coe_slConjugation]
  rfl

theorem coe_mul_coe_inv (g : SpecialLinearGroup (Fin 4) F) :
    (g : Matrix (Fin 4) (Fin 4) F) *
      ((g⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_inv_mul_coe (g : SpecialLinearGroup (Fin 4) F) :
    ((g⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (g : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem mem_fixOf_graphLift_iff (A : GL (Fin 4) F) (g : SpecialLinearGroup (Fin 4) F) :
    g ∈ CatFactsSp4.fixOf (graphLift A) ↔
      (g : Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (g : Matrix (Fin 4) (Fin 4) F) = ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  set G := (g : Matrix (Fin 4) (Fin 4) F) with hG
  set Gi := ((g⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hGi
  set R := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hR
  have hAR : (A : Matrix (Fin 4) (Fin 4) F) * R = 1 := by
    rw [hR, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRA : R * (A : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [hR, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGGi : G * Gi = 1 := coe_mul_coe_inv g
  have hGiG : Gi * G = 1 := coe_inv_mul_coe g
  rw [CatFactsSp4.mem_fixOf]
  constructor
  · intro hg
    have h := congrArg (fun x : SpecialLinearGroup (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F)) hg
    simp only [coe_graphLift] at h
    calc Gᵀ * R * G = Gᵀ * R * ((A : Matrix (Fin 4) (Fin 4) F) * Giᵀ * R) := by rw [h]
      _ = Gᵀ * (R * (A : Matrix (Fin 4) (Fin 4) F)) * Giᵀ * R := by
          simp only [Matrix.mul_assoc]
      _ = (Gi * G)ᵀ * R := by rw [hRA, Matrix.mul_one, Matrix.transpose_mul]
      _ = R := by rw [hGiG, transpose_one, Matrix.one_mul]
  · intro hg
    apply Subtype.ext
    rw [coe_graphLift]
    have hRG : R * G = Giᵀ * R := by
      calc R * G = (G * Gi)ᵀ * (R * G) := by rw [hGGi, transpose_one, Matrix.one_mul]
        _ = Giᵀ * (Gᵀ * R * G) := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
        _ = Giᵀ * R := by rw [hg]
    calc (A : Matrix (Fin 4) (Fin 4) F) * Giᵀ * R = (A : Matrix (Fin 4) (Fin 4) F) * (Giᵀ * R) :=
          Matrix.mul_assoc _ _ _
      _ = (A : Matrix (Fin 4) (Fin 4) F) * (R * G) := by rw [hRG]
      _ = G := by rw [← Matrix.mul_assoc, hAR, Matrix.one_mul]

theorem isometry_of_mem_fixOf_graphLift (A : GL (Fin 4) F) {g : SpecialLinearGroup (Fin 4) F}
    (hg : g ∈ CatFactsSp4.fixOf (graphLift A)) :
    (g : Matrix (Fin 4) (Fin 4) F) * A * (g : Matrix (Fin 4) (Fin 4) F)ᵀ = A := by
  have h := congrArg (fun x : SpecialLinearGroup (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F))
    (CatFactsSp4.mem_fixOf.mp hg)
  simp only [coe_graphLift] at h
  have hRA : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (g : Matrix (Fin 4) (Fin 4) F) * A * (g : Matrix (Fin 4) (Fin 4) F)ᵀ =
        (A : Matrix (Fin 4) (Fin 4) F) *
          ((g⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
          ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * A *
          (g : Matrix (Fin 4) (Fin 4) F)ᵀ := by rw [h]
    _ = (A : Matrix (Fin 4) (Fin 4) F) * ((g : Matrix (Fin 4) (Fin 4) F) *
          ((g⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))ᵀ := by
        rw [Matrix.mul_assoc _ ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F), hRA,
          Matrix.mul_one, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = A := by rw [coe_mul_coe_inv, transpose_one, Matrix.mul_one]

theorem negOne4_mem_fixOf_graphLift (A : GL (Fin 4) F) :
    negOne4 ∈ CatFactsSp4.fixOf (graphLift A) := by
  rw [mem_fixOf_graphLift_iff]
  change (-1 : Matrix (Fin 4) (Fin 4) F)ᵀ * _ * (-1) = _
  simp only [transpose_neg, transpose_one, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.one_mul,
    Matrix.mul_one]

theorem det_glEquiv (G : GL (Fin 4) F) :
    LinearEquiv.det (StabL.glEquiv G) = GeneralLinearGroup.det G := by
  apply Units.ext
  rw [LinearEquiv.coe_det, GeneralLinearGroup.val_det_apply]
  have h : (StabL.glEquiv G : (Fin 4 → F) →ₗ[F] (Fin 4 → F)) =
      Matrix.toLin' (G : Matrix (Fin 4) (Fin 4) F) :=
    LinearMap.ext fun v => by
      rw [LinearEquiv.coe_coe, StabL.glEquiv_apply, Matrix.toLin'_apply]
  rw [h, LinearMap.det_toLin']

theorem exists_anisotropic (h2 : (2 : F) ≠ 0) {R : Matrix (Fin 4) (Fin 4) F} (hR : Rᵀ = R)
    (hRu : IsUnit R.det) : ∃ v, Matrix.toQuadraticForm' R v ≠ 0 := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  have hpol : QuadraticMap.polarBilin (Matrix.toQuadraticForm' R) = 0 := by
    refine LinearMap.ext₂ fun x y => ?_
    simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h]
  rw [StabL.polarBilin_toQuadraticForm' hR] at hpol
  have h0 : (2 : F) • R = 0 := Matrix.toBilin'.injective (by rw [hpol, map_zero])
  have hR0 : R = 0 := (smul_eq_zero.mp h0).resolve_left h2
  rw [hR0, det_zero] at hRu
  exact not_isUnit_zero hRu

theorem card_orthogonalGroup_dvd [Finite F] (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F))
    {R : Matrix (Fin 4) (Fin 4) F} (hR : Rᵀ = R) (hRu : IsUnit R.det) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Matrix.toQuadraticForm' R)) ∣
      Nat.card F ^ 2 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1)) := by
  set Q := Matrix.toQuadraticForm' R with hQ
  have hnd : (QuadraticMap.polarBilin Q).Nondegenerate := by
    rw [hQ, StabL.polarBilin_toQuadraticForm' hR]
    apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2
    rw [Matrix.det_smul, Fintype.card_fin]
    exact mul_ne_zero (pow_ne_zero _ h2) hRu.ne_zero
  have hdim : Module.finrank F (Fin 4 → F) = 2 * (1 + 1) := by rw [Module.finrank_fin_fun]
  obtain ⟨t, ht⟩ := hodd
  have hq1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  have hq4 : 1 ≤ Nat.card F ^ 4 := Nat.one_le_pow _ _ Nat.card_pos
  by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType Q
  · have hO := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hnd hdim
      (Or.inl ⟨rfl, hp⟩)
    refine ⟨2 * t * t + 2 * t + 1, ?_⟩
    have key : ((Nat.card F ^ 2 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1)) : ℕ) : ℤ) =
        ((Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) * (2 * t * t + 2 * t + 1) : ℕ) :
          ℤ) := by
      push_cast [hq1, hq4]
      rw [hO]
      simp only [Finset.Icc_self, Finset.prod_singleton]
      rw [ht]
      push_cast
      ring
    exact_mod_cast key
  · have hO := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hnd hdim
      (Or.inr ⟨rfl, hp⟩)
    refine ⟨2 * t * t + 2 * t, ?_⟩
    have key : ((Nat.card F ^ 2 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1)) : ℕ) : ℤ) =
        ((Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) * (2 * t * t + 2 * t) : ℕ) : ℤ) := by
      push_cast [hq1, hq4]
      rw [hO]
      simp only [Finset.Icc_self, Finset.prod_singleton]
      rw [ht]
      push_cast
      ring
    exact_mod_cast key

theorem orderOf_neg_one_units (h2 : (2 : F) ≠ 0) : orderOf (-1 : Fˣ) = 2 := by
  refine orderOf_eq_prime (by rw [neg_one_sq]) fun h => h2 ?_
  have h1 := congrArg Units.val h
  rw [Units.val_neg, Units.val_one] at h1
  linear_combination -h1

theorem two_mul_card_specialOrthogonalWithin_dvd [Finite F] (h2 : (2 : F) ≠ 0)
    {R : Matrix (Fin 4) (Fin 4) F} (hR : Rᵀ = R) (hRu : IsUnit R.det) :
    2 * Nat.card (QuadraticMap.specialOrthogonalWithin (Matrix.toQuadraticForm' R)) ∣
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Matrix.toQuadraticForm' R)) := by
  set Q := Matrix.toQuadraticForm' R with hQ
  obtain ⟨v, hv⟩ := exists_anisotropic h2 hR hRu
  let _ : Invertible (Q v) := invertibleOfNonzero hv
  have hr : TauCeti.QuadraticMap.reflection Q v ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q v
  have hdr : QuadraticMap.orthogonalDet Q ⟨_, hr⟩ = -1 := by
    rw [QuadraticMap.orthogonalDet_apply]
    exact TauCeti.QuadraticMap.det_reflection Q v
  have ho : orderOf (⟨-1, ⟨_, hr⟩, hdr⟩ : (QuadraticMap.orthogonalDet Q).range) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_neg_one_units h2
  have h2r : 2 ∣ Nat.card (QuadraticMap.orthogonalDet Q).range := ho ▸ orderOf_dvd_natCard _
  have hSO : QuadraticMap.specialOrthogonalWithin Q = (QuadraticMap.orthogonalDet Q).ker := by
    ext g
    rw [QuadraticMap.mem_specialOrthogonalWithin_iff, MonoidHom.mem_ker,
      QuadraticMap.orthogonalDet_apply]
  rw [hSO, ← Subgroup.card_ker_mul_card_range (QuadraticMap.orthogonalDet Q), mul_comm]
  exact Nat.mul_dvd_mul_left _ h2r

theorem four_mul_card_dvd_of_symmetric [Finite F] (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F))
    (A : GL (Fin 4) F) (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A)
    {M : Subgroup (projectiveSL 4 F)} (hM : ⁅M, M⁆ = M)
    (hfix : ∀ x ∈ M, (conjAut 4 F A * dualAut 4 F) x = x) :
    4 * Nat.card M ∣ Nat.card F ^ 2 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1)) := by
  classical
  set R := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hRdef
  have hRt : Rᵀ = R := by
    rw [hRdef, Matrix.coe_units_inv, Matrix.transpose_nonsing_inv, hA]
  have hRu : IsUnit R.det := by
    rw [hRdef, ← GeneralLinearGroup.val_det_apply]
    exact Units.isUnit _
  set Q := Matrix.toQuadraticForm' R with hQ
  set C := CatFactsSp4.fixOf (graphLift A) with hC
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  have hmem : ∀ g : C,
      StabL.glEquiv (SpecialLinearGroup.toGL (g : SpecialLinearGroup (Fin 4) F)) ∈ O :=
    fun g => StabL.glEquiv_mem_orthogonalGroup (isometry_of_mem_fixOf_graphLift A g.2)
  set Ψ : GL (Fin 4) F →* ((Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 4 → F)).toMonoidHom.comp
      (GeneralLinearGroup.toLin).toMonoidHom with hΨ
  have hΨg : ∀ G, Ψ G = StabL.glEquiv G := fun G => rfl
  set Φ : C →* O := (Ψ.comp (SpecialLinearGroup.toGL.comp C.subtype)).codRestrict O
    (fun g => by
      change Ψ (SpecialLinearGroup.toGL (g : SpecialLinearGroup (Fin 4) F)) ∈ O
      rw [hΨg]
      exact hmem g) with hΦ
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    change Ψ (SpecialLinearGroup.toGL (x : SpecialLinearGroup (Fin 4) F)) =
      Ψ (SpecialLinearGroup.toGL (y : SpecialLinearGroup (Fin 4) F)) at h1
    rw [hΨg, hΨg] at h1
    exact Subtype.ext (SpecialLinearGroup.toGL_injective (StabL.glEquiv_injective h1))
  have hrange : Φ.range ≤ QuadraticMap.specialOrthogonalWithin Q := by
    rintro _ ⟨g, rfl⟩
    rw [QuadraticMap.mem_specialOrthogonalWithin_iff]
    change LinearEquiv.det (Ψ (SpecialLinearGroup.toGL (g : SpecialLinearGroup (Fin 4) F))) = 1
    rw [hΨg, det_glEquiv]
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Units.val_one]
    exact (g : SpecialLinearGroup (Fin 4) F).2
  have hC2 : 2 * Nat.card C ∣ Nat.card O := by
    rw [Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv]
    exact (Nat.mul_dvd_mul_left 2 (Subgroup.card_dvd_of_le hrange)).trans
      (two_mul_card_specialOrthogonalWithin_dvd h2 hRt hRu)
  have h1 : M ≤ C.map (proj 4 F) := perfect_le_map_fixOf_proj _ (graphLift_proj A) hM hfix
  have h3 := two_mul_card_map_proj_dvd h2 (negOne4_mem_fixOf_graphLift A)
  have h4 := card_orthogonalGroup_dvd h2 hodd hRt hRu
  calc 4 * Nat.card M ∣ 2 * (2 * Nat.card (C.map (proj 4 F))) := by
        rw [← mul_assoc]
        exact Nat.mul_dvd_mul_left 4 (Subgroup.card_dvd_of_le h1)
    _ ∣ 2 * Nat.card C := Nat.mul_dvd_mul_left 2 h3
    _ ∣ Nat.card O := hC2
    _ ∣ _ := h4

end CFSG.ComponentClassification.GSThmB.P211
