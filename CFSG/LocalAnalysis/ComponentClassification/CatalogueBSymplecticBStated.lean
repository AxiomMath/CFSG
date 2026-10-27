module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBFieldConjugation

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticB

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)

variable {r : ℕ} {K : Type} [Field K]

@[expose] def matrixLinIso :
    GL (Fin r ⊕ Fin r) K ≃* ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K _)

theorem matrixLinIso_apply (A : GL (Fin r ⊕ Fin r) K) (v : Fin r ⊕ Fin r → K) :
    matrixLinIso A v = (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v := rfl

theorem matrixLinIso_symm_apply (A : GL (Fin r ⊕ Fin r) K) (v : Fin r ⊕ Fin r → K) :
    (matrixLinIso A).symm v = ((A⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v := by
  change (matrixLinIso A)⁻¹ v = _
  rw [← map_inv]
  rfl

theorem matrixLinIso_scalar (c : Kˣ) (v : Fin r ⊕ Fin r → K) :
    matrixLinIso (GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c) v = (c : K) • v := by
  rw [matrixLinIso_apply]
  funext i
  simp [GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal]

theorem matrixLinIso_scalar_neg_one :
    matrixLinIso (GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (-1 : Kˣ)) = LinearEquiv.neg K := by
  apply LinearEquiv.ext
  intro v
  rw [matrixLinIso_scalar]
  simp

theorem eq_scalar_of_matrixLinIso_apply (A : GL (Fin r ⊕ Fin r) K) (b : Kˣ)
    (h : ∀ x, matrixLinIso A x = (b : K) • x) :
    A = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) b := by
  apply matrixLinIso.injective
  apply LinearEquiv.ext
  intro x
  rw [h x, matrixLinIso_scalar]

theorem matrixLinIso_ne_smul_one (A : GL (Fin r ⊕ Fin r) K)
    (hA : ∀ c : Kˣ, A ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c) (a : K) :
    (matrixLinIso A).toLinearMap ≠ a • (1 : Module.End K (Fin r ⊕ Fin r → K)) := by
  intro h
  have happly : ∀ x, matrixLinIso A x = a • x := fun x => LinearMap.congr_fun h x
  by_cases ha : a = 0
  · refine hA 1 (eq_scalar_of_matrixLinIso_apply A 1 fun x => ?_)
    have hx : x = 0 := (matrixLinIso A).injective (by rw [happly, ha, zero_smul, map_zero])
    rw [hx, map_zero, smul_zero]
  · exact hA (Units.mk0 a ha) (eq_scalar_of_matrixLinIso_apply A _ happly)

theorem pairedSympForm_mulVec_eq_toBilin' (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (u v : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (A *ᵥ u) (A *ᵥ v) = Matrix.toBilin' (Aᵀ * formJ r K * A) u v := by
  simp only [pairedSympForm, toBilin'_apply']
  rw [mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, ← Matrix.mul_assoc,
    ← dotProduct_mulVec]

theorem mem_statedSp_iff_isometry (A : GL (Fin r ⊕ Fin r) K) :
    A ∈ StatedSp r K ↔ matrixLinIso A ∈ isometryGroup (pairedSympForm K r) := by
  rw [SymplecticTorusWeyl.mem_statedSp_iff, mem_isometryGroup_iff]
  simp only [matrixLinIso_apply, pairedSympForm_mulVec_eq_toBilin']
  constructor
  · intro h u v
    rw [h]
    rfl
  · intro h
    apply Matrix.toBilin'.injective
    exact LinearMap.ext fun u => LinearMap.ext fun v => h u v

@[expose] def statedSpIsometryEquiv : StatedSp r K ≃* isometryGroup (pairedSympForm K r) where
  toFun g := ⟨matrixLinIso g.val, (mem_statedSp_iff_isometry g.val).mp g.property⟩
  invFun h := ⟨matrixLinIso.symm h.val, (mem_statedSp_iff_isometry _).mpr (by
    rw [MulEquiv.apply_symm_apply]
    exact h.property)⟩
  left_inv g := Subtype.ext (matrixLinIso.symm_apply_apply g.val)
  right_inv h := Subtype.ext (matrixLinIso.apply_symm_apply h.val)
  map_mul' g h := Subtype.ext (map_mul matrixLinIso g.val h.val)

theorem statedSpIsometryEquiv_val (g : StatedSp r K) :
    (statedSpIsometryEquiv g).val = matrixLinIso g.val := rfl

theorem statedSpIsometryEquiv_symm_val (h : isometryGroup (pairedSympForm K r)) :
    (statedSpIsometryEquiv.symm h).val = matrixLinIso.symm h.val := rfl

theorem spScalars_map (hr : 1 ≤ r) :
    (spScalars r K).map statedSpIsometryEquiv.toMonoidHom = scalarSigns (pairedSympForm K r) := by
  ext h
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range,
    statedSpIsometryEquiv_symm_val, mem_scalarSigns_iff]
  constructor
  · rintro ⟨c, hc⟩
    have hh : h.val = matrixLinIso (GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c) := by
      rw [hc, MulEquiv.apply_symm_apply]
    have hiso := (mem_isometryGroup_iff _ _).mp h.property
      (Pi.single (Sum.inl ⟨0, hr⟩) 1) (Pi.single (Sum.inr ⟨0, hr⟩) 1)
    rw [hh, matrixLinIso_scalar, matrixLinIso_scalar, LinearMap.map_smul₂,
      LinearMap.map_smul, smul_eq_mul, smul_eq_mul, pairedSympForm_single, mul_one] at hiso
    rcases mul_self_eq_one_iff.mp hiso with h1 | h1
    · left
      apply Subtype.ext
      rw [hh, show c = 1 from Units.ext h1, map_one, map_one]
      rfl
    · right
      apply Subtype.ext
      rw [hh, show c = -1 from Units.ext (by simpa using h1), matrixLinIso_scalar_neg_one]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨1, by rw [map_one]; exact (map_one matrixLinIso.symm).symm⟩
    · refine ⟨-1, ?_⟩
      rw [MulEquiv.eq_symm_apply, matrixLinIso_scalar_neg_one]
      rfl

@[expose] def projectiveStatedEquiv (hr : 1 ≤ r) :
    StatedProj (StatedSp r K) ≃* projectiveSymplectic (pairedSympForm K r) :=
  QuotientGroup.congr (spScalars r K) (scalarSigns (pairedSympForm K r)) statedSpIsometryEquiv
    (spScalars_map hr)

theorem projectiveStatedEquiv_proj (hr : 1 ≤ r) (g : StatedSp r K) :
    projectiveStatedEquiv hr (proj r K g) =
      QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) (statedSpIsometryEquiv g) :=
  QuotientGroup.congr_mk' _ _ _ _ g

theorem matrix_similitude (A : GL (Fin r ⊕ Fin r) K) (μ : Kˣ)
    (hμ : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * A =
      (μ : K) • formJ r K) (x y : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (matrixLinIso A x) (matrixLinIso A y) =
      (μ : K) * pairedSympForm K r x y :=
  pairedSympForm_mulVec_of_formJ hμ x y

theorem projectiveStatedEquiv_conjAut (hr : 1 ≤ r) (A : gsp r K) (μ : Kˣ)
    (hμ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      formJ r K * ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (μ : K) • formJ r K) (x : StatedProj (StatedSp r K)) :
    projectiveStatedEquiv hr (conjAut r K A x) =
      projectiveConjugation (pairedSympForm K r) (matrixLinIso (A : GL (Fin r ⊕ Fin r) K)) μ
        (matrix_similitude _ μ hμ) (projectiveStatedEquiv hr x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
  change projectiveStatedEquiv hr (conjAut r K A (proj r K g)) =
    projectiveConjugation _ _ μ _ (projectiveStatedEquiv hr (proj r K g))
  rw [conjAut_proj, projectiveStatedEquiv_proj, projectiveStatedEquiv_proj,
    projectiveConjugation_mk]
  congr 1
  apply Subtype.ext
  rw [statedSpIsometryEquiv_val, similitudeConjugation_val, statedSpIsometryEquiv_val,
    coe_conjSp, map_mul, map_mul, map_inv]

@[expose] def coordFieldMap (σ : K ≃+* K) : (Fin r ⊕ Fin r → K) ≃+ (Fin r ⊕ Fin r → K) where
  toFun v i := σ (v i)
  invFun v i := σ.symm (v i)
  left_inv v := by funext i; exact σ.symm_apply_apply (v i)
  right_inv v := by funext i; exact σ.apply_symm_apply (v i)
  map_add' v w := by funext i; exact σ.map_add (v i) (w i)

theorem coordFieldMap_apply (σ : K ≃+* K) (v : Fin r ⊕ Fin r → K) :
    coordFieldMap σ v = fun i => σ (v i) := rfl

@[expose] def semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) (σ : K ≃+* K) :
    (Fin r ⊕ Fin r → K) ≃+ (Fin r ⊕ Fin r → K) :=
  (coordFieldMap σ).trans (matrixLinIso A).toAddEquiv

theorem semilinearCoordMap_apply (A : GL (Fin r ⊕ Fin r) K) (σ : K ≃+* K)
    (v : Fin r ⊕ Fin r → K) :
    semilinearCoordMap A σ v =
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ fun i => σ (v i) := rfl

theorem semilinearCoordMap_symm_apply (A : GL (Fin r ⊕ Fin r) K) (σ : K ≃+* K)
    (v : Fin r ⊕ Fin r → K) :
    (semilinearCoordMap A σ).symm v = fun i => σ.symm ((matrixLinIso A).symm v i) := rfl

theorem semilinearCoordMap_smul (A : GL (Fin r ⊕ Fin r) K) (σ : K ≃+* K) (a : K)
    (v : Fin r ⊕ Fin r → K) :
    semilinearCoordMap A σ (a • v) = σ a • semilinearCoordMap A σ v := by
  rw [semilinearCoordMap_apply, semilinearCoordMap_apply, ← mulVec_smul]
  congr 1
  funext i
  simp

theorem semilinearCoordMap_form (A : GL (Fin r ⊕ Fin r) K) (σ : K ≃+* K) (μ : Kˣ)
    (hμ : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * A =
      (μ : K) • formJ r K) (x y : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (semilinearCoordMap A σ x) (semilinearCoordMap A σ y) =
      (μ : K) * σ (pairedSympForm K r x y) := by
  rw [semilinearCoordMap_apply, semilinearCoordMap_apply, pairedSympForm_mulVec_of_formJ hμ,
    pairedSympForm_map]

theorem coord_mulVec (σ : K ≃+* K) (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (w : Fin r ⊕ Fin r → K) :
    (fun i => σ ((M *ᵥ w) i)) = M.map σ *ᵥ fun i => σ (w i) := by
  funext i
  exact RingHom.map_mulVec σ.toRingHom M w i

theorem semilinearCoordMap_sq (A : GL (Fin r ⊕ Fin r) K) (σ : K ≃+* K) (hσ : σ ^ 2 = 1)
    (d : Kˣ)
    (hd : A * glFieldEquiv (Fin r ⊕ Fin r) σ A = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d)
    (v : Fin r ⊕ Fin r → K) :
    semilinearCoordMap A σ (semilinearCoordMap A σ v) = (d : K) • v := by
  have hσσ : ∀ c : K, σ (σ c) = c := fun c => by
    have := congrArg (fun τ : K ≃+* K => τ c) hσ
    simpa [sq] using this
  rw [semilinearCoordMap_apply, semilinearCoordMap_apply, coord_mulVec, mulVec_mulVec]
  have hv : (fun i => σ (σ (v i))) = v := funext fun i => hσσ (v i)
  rw [hv, ← matrixLinIso_scalar, ← hd, matrixLinIso_apply]
  rfl

theorem projectiveStatedEquiv_conjAut_fieldAut (hr : 1 ≤ r) (A : gsp r K) (σ : K ≃+* K)
    (μ : Kˣ)
    (hμ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      formJ r K * ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (μ : K) • formJ r K) (x : StatedProj (StatedSp r K)) :
    projectiveStatedEquiv hr ((conjAut r K A * fieldAut r K σ) x) =
      projectiveSemilinearConjugation (pairedSympForm K r) σ
        (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
        (semilinearCoordMap_form _ σ μ hμ) (projectiveStatedEquiv hr x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
  change projectiveStatedEquiv hr (conjAut r K A (fieldAut r K σ (proj r K g))) =
    projectiveSemilinearConjugation _ σ _ μ _ _ (projectiveStatedEquiv hr (proj r K g))
  rw [fieldAut_proj, conjAut_proj, projectiveStatedEquiv_proj, projectiveStatedEquiv_proj,
    projectiveSemilinearConjugation_mk]
  congr 1
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change ((((conjSp r K A (fieldSp r K σ g) : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) =
    semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ
      (((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ).symm v)
  rw [coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp, semilinearCoordMap_apply,
    coord_mulVec, semilinearCoordMap_symm_apply]
  have hσ : (fun i => σ (σ.symm ((matrixLinIso (A : GL (Fin r ⊕ Fin r) K)).symm v i))) =
      (matrixLinIso (A : GL (Fin r ⊕ Fin r) K)).symm v :=
    funext fun i => σ.apply_symm_apply _
  rw [hσ, matrixLinIso_symm_apply, mulVec_mulVec, mulVec_mulVec]

end CFSG.ComponentClassification.CatalogueBSymplecticB
