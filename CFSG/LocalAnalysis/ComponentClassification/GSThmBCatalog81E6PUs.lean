module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PUf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PLs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PUt

public section

namespace CFSG.ComponentClassification.GSThmB.P211

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.CatFactsL4U4 UnitaryOut UnitaryConj HBlocks
  ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.LinearGroups StabU

theorem glEquiv_mem_orthogonalGroup' {F : Type} [Field F] {R : Matrix (Fin 4) (Fin 4) F}
    {X : GL (Fin 4) F} (hX : (X : Matrix (Fin 4) (Fin 4) F)ᵀ * R * X = R) :
    StabL.glEquiv X ∈ TauCeti.QuadraticMap.orthogonalGroup (Matrix.toQuadraticForm' R) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', StabL.glEquiv_apply]
  have key : ∀ w : Fin 4 → F, ((X : Matrix (Fin 4) (Fin 4) F) *ᵥ v) ⬝ᵥ w =
      v ⬝ᵥ ((X : Matrix (Fin 4) (Fin 4) F)ᵀ *ᵥ w) := by
    intro w
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.mulVec_transpose]
  rw [key, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hX]

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem four_mul_card_dvd_of_symm_U4 (hp2 : p ≠ 2) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = 1)
    (ψ : unitarySU p f K 4 →* unitarySU p f K 4)
    (hψv : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K))
    {M : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hMle : M ≤ (ψ.eqLocus (MonoidHom.id _)).map (QuotientGroup.mk' (scal p f K))) :
    4 * Nat.card M ∣ (p ^ f) ^ 2 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨Rm, G, l, hGt, hGdet, hl0, hR1, hR2⟩ := exists_real_frame_symm h hp2 hAu hAA
  have hGK : (G.map h.fixedField.subtype).det ≠ 0 := by
    rw [show G.map h.fixedField.subtype = h.fixedField.subtype.mapMatrix G from rfl,
      ← RingHom.map_det]
    exact (map_ne_zero _).2 hGdet
  have hRdet : Rm.det ≠ 0 := by
    intro h0
    apply hGK
    rw [← hR1, det_mul, h0, mul_zero]
  set R : GL (Fin 4) K := GeneralLinearGroup.mkOfDetNeZero Rm hRdet with hRdef
  have hRv : (R : Matrix (Fin 4) (Fin 4) K) = Rm := GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hRR : (R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRiR : (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hR1' : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
      G.map h.fixedField.subtype := by rw [hRv]; exact hR1
  have hA1 : (A : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K).map h.bar =
      l⁻¹ • (R : Matrix (Fin 4) (Fin 4) K) := by
    rw [hRv]
    conv_rhs => rw [← hR2]
    rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have hAA' : (A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAiA : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hRb : (R : Matrix (Fin 4) (Fin 4) K).map h.bar *
      (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar = 1 := by
    rw [← Matrix.map_mul, hRR, Matrix.map_one _ (map_zero _) (map_one _)]
  have hB : (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) =
      l • (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
    calc (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) =
        (l • (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) * (l⁻¹ • (R : Matrix (Fin 4) (Fin 4) K)) *
          ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul, hRiR, smul_smul, mul_inv_cancel₀ hl0, one_smul,
            Matrix.one_mul]
      _ = (l • (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) * ((A : Matrix (Fin 4) (Fin 4) K) *
          ((R : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar) *
            (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
          rw [← hA1]
          simp only [Matrix.mul_assoc]
      _ = l • (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by rw [hRb, Matrix.mul_one, hAA', Matrix.mul_one]
  set Q := Matrix.toQuadraticForm' G with hQ
  set Ψ : GL (Fin 4) h.fixedField →*
      ((Fin 4 → h.fixedField) ≃ₗ[h.fixedField] (Fin 4 → h.fixedField)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv h.fixedField
      (Fin 4 → h.fixedField)).toMonoidHom.comp (GeneralLinearGroup.toLin).toMonoidHom with hΨ
  have hΨg : ∀ X, Ψ X = StabL.glEquiv X := fun X => rfl
  have hΨinj : Function.Injective Ψ := fun X Y hXY => StabL.glEquiv_injective hXY
  set S := (TauCeti.QuadraticMap.specialOrthogonalGroup Q).comap Ψ with hS
  set ι₀ : GL (Fin 4) h.fixedField →* GL (Fin 4) K :=
    (MulAut.conj R).toMonoidHom.comp (glIncl h) with hι₀
  have hι₀v : ∀ X, ((ι₀ X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) * (X : Matrix (Fin 4) (Fin 4) h.fixedField).map
        h.fixedField.subtype * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := fun X => by
    rw [hι₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul,
      Units.val_mul, coe_glIncl]
  have hι₀inj : Function.Injective ι₀ := by
    intro X Y hXY
    have e := congrArg (fun Z : GL (Fin 4) K => (Z : Matrix (Fin 4) (Fin 4) K)) hXY
    simp only [hι₀v] at e
    have e' := congrArg (fun Z => (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * Z *
      (R : Matrix (Fin 4) (Fin 4) K)) e
    simp only [inv_mul_val_mul] at e'
    exact Units.ext (Matrix.map_injective h.fixedField.subtype.injective e')
  set C := ψ.eqLocus (MonoidHom.id _) with hC
  have hCS : C.map (unitarySU p f K 4).subtype ≤ S.map ι₀ := by
    rintro _ ⟨g, hg, rfl⟩
    change ψ g = g at hg
    set Gg := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hGgdef
    have hgG : (A : Matrix (Fin 4) (Fin 4) K) * Gg.map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) =
        Gg := by
      rw [← hψv, hg]
    have hGb : Gg.map h.bar = (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * Gg * A := by
      calc Gg.map h.bar = (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((A : Matrix (Fin 4) (Fin 4) K) *
            Gg.map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) * A := by
            simp only [← Matrix.mul_assoc]
            rw [hAiA, Matrix.one_mul, Matrix.mul_assoc, hAiA, Matrix.mul_one]
        _ = (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * Gg * A := by rw [hgG]
    obtain ⟨hGdet', hGu⟩ := (mem_unitarySU_iff h).1 g.2
    set X := (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * Gg * R with hXdef
    have hXb : X.map h.bar = X := by
      rw [hXdef, Matrix.map_mul, Matrix.map_mul, hGb]
      calc (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar *
            ((↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * Gg * A) *
              (R : Matrix (Fin 4) (Fin 4) K).map h.bar =
          ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) * Gg *
            ((A : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K).map h.bar) := by
            simp only [Matrix.mul_assoc]
        _ = (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * Gg * R := by
            rw [hB, hA1, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
              inv_mul_cancel₀ hl0, one_smul]
    have hXmem : ∀ i j, X i j ∈ h.fixedField := fun i j =>
      (h.mem_fixedField).2 (by
        have := congrFun (congrFun hXb i) j
        rwa [Matrix.map_apply] at this)
    set X' : Matrix (Fin 4) (Fin 4) h.fixedField := Matrix.of fun i j => ⟨X i j, hXmem i j⟩
      with hX'def
    have hX'X : X'.map h.fixedField.subtype = X := by
      ext i j
      rfl
    have hXdet : X.det = 1 := by
      rw [hXdef, det_mul, det_mul, mul_comm ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).det), mul_assoc,
        ← det_mul, hRiR, det_one, mul_one]
      exact hGdet'
    have hX'det : X'.det = 1 := by
      apply h.fixedField.subtype.injective
      rw [map_one, RingHom.map_det,
        show h.fixedField.subtype.mapMatrix X' = X'.map h.fixedField.subtype from rfl, hX'X,
        hXdet]
    have hRi : uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * uStar h (R : Matrix (Fin 4) (Fin 4) K)
        = 1 := by rw [← uStar_mul, hRR, uStar_one]
    have hXu : uStar h X * (G.map h.fixedField.subtype) * X = G.map h.fixedField.subtype := by
      rw [← hR1', hXdef, uStar_mul, uStar_mul]
      calc uStar h (R : Matrix (Fin 4) (Fin 4) K) * (uStar h Gg *
            uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) *
            (uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K)) *
            ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * Gg * R) =
          uStar h (R : Matrix (Fin 4) (Fin 4) K) * uStar h Gg *
            (uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) *
              uStar h (R : Matrix (Fin 4) (Fin 4) K)) *
            ((R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) * Gg * R := by
            simp only [Matrix.mul_assoc]
        _ = uStar h (R : Matrix (Fin 4) (Fin 4) K) * R := by
            have hGu' : uStar h Gg * Gg = 1 := hGu
            rw [hRi, hRR, Matrix.mul_one, Matrix.mul_one]
            simp only [Matrix.mul_assoc] at hGu' ⊢
            rw [← Matrix.mul_assoc (uStar h Gg), hGu', Matrix.one_mul]
    have hXs : Xᵀ * (G.map h.fixedField.subtype) * X = G.map h.fixedField.subtype := by
      have hXt : uStar h X = Xᵀ := by rw [uStar, hXb]
      rwa [hXt] at hXu
    have hX's : X'ᵀ * G * X' = G := by
      apply Matrix.map_injective h.fixedField.subtype.injective
      dsimp only
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hX'X]
      exact hXs
    have hX'0 : X'.det ≠ 0 := by rw [hX'det]; exact one_ne_zero
    set N : GL (Fin 4) h.fixedField := GeneralLinearGroup.mkOfDetNeZero X' hX'0 with hN
    have hNv : (N : Matrix (Fin 4) (Fin 4) h.fixedField) = X' :=
      GeneralLinearGroup.val_mkOfDetNeZero _ _
    have hNS : N ∈ S := by
      rw [hS, Subgroup.mem_comap, TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff, hΨg]
      refine ⟨glEquiv_mem_orthogonalGroup' (by rw [hNv]; exact hX's), ?_⟩
      rw [det_glEquiv]
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, Units.val_one, hNv, hX'det]
    refine ⟨N, hNS, Units.ext ?_⟩
    rw [hι₀v, hNv, hX'X, hXdef]
    change (R : Matrix (Fin 4) (Fin 4) K) * ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * Gg * R) *
      (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) = Gg
    calc (R : Matrix (Fin 4) (Fin 4) K) * ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * Gg * R) *
          (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) =
        ((R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) * Gg *
          ((R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
          simp only [Matrix.mul_assoc]
      _ = Gg := by rw [hRR, Matrix.one_mul, Matrix.mul_one]
  have hcardC : Nat.card C ∣ Nat.card S := by
    rw [← Subgroup.card_map_of_injective (unitarySU p f K 4).subtype_injective,
      ← Subgroup.card_map_of_injective hι₀inj]
    exact Subgroup.card_dvd_of_le hCS
  have hcardS : Nat.card S ∣ Nat.card (TauCeti.QuadraticMap.specialOrthogonalGroup Q) := by
    rw [← Subgroup.card_map_of_injective hΨinj]
    exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
  have hSO : Nat.card (TauCeti.QuadraticMap.specialOrthogonalGroup Q) =
      Nat.card (QuadraticMap.specialOrthogonalWithin Q) :=
    Nat.card_congr (QuadraticMap.specialOrthogonalWithinEquiv Q).symm.toEquiv
  have h2F : (2 : h.fixedField) ≠ 0 := by
    intro h0
    apply h2K
    have := congrArg h.fixedField.subtype h0
    rwa [map_ofNat, map_zero] at this
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hGdet
  have hodd : Odd (Nat.card h.fixedField) := by
    rw [h.card_fixedField]
    exact (h.prime.odd_of_ne_two hp2).pow
  have hO := card_orthogonalGroup_dvd h2F hodd hGt hGu
  have hSO2 := two_mul_card_specialOrthogonalWithin_dvd h2F hGt hGu
  rw [h.card_fixedField] at hO
  have hneg : negOne h ∈ C := by
    change ψ (negOne h) = negOne h
    apply ext_val
    rw [hψv]
    change (A : Matrix (Fin 4) (Fin 4) K) * (-1 : Matrix (Fin 4) (Fin 4) K).map h.bar *
      (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = -1
    rw [Matrix.map_neg _ (map_neg h.bar), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hAA']
  have hneg2 : orderOf (negOne h) = 2 := by
    refine orderOf_eq_prime ?_ (negOne_ne_one h h2K)
    rw [sq]
    apply ext_val
    change (-1 : Matrix (Fin 4) (Fin 4) K) * (-1) = 1
    rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.one_mul]
  have h3 := two_mul_card_map_dvd (π := QuotientGroup.mk' (scal p f K)) hneg
    ((QuotientGroup.eq_one_iff _).2 (negOne_mem_scal h)) hneg2
  calc 4 * Nat.card M ∣ 2 * (2 * Nat.card (C.map (QuotientGroup.mk' (scal p f K)))) := by
        rw [← mul_assoc]
        exact Nat.mul_dvd_mul_left 4 (Subgroup.card_dvd_of_le hMle)
    _ ∣ 2 * Nat.card C := Nat.mul_dvd_mul_left 2 h3
    _ ∣ 2 * Nat.card (QuadraticMap.specialOrthogonalWithin Q) :=
        Nat.mul_dvd_mul_left 2 (hSO ▸ hcardC.trans hcardS)
    _ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := hSO2
    _ ∣ _ := hO

end CFSG.ComponentClassification.GSThmB.P211
