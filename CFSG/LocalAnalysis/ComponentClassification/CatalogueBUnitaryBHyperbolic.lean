module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBSemilinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFourGroupTransport

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryB

open Matrix Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

section FixedInf

variable {P D : Type*} [Group P] [Group D]

@[expose] def fixedEquivInf (N : Subgroup D) (e : P ≃* N) (β : MulAut P) (ψ : MulAut D)
    (he : ∀ y, ((e (β y) : N) : D) = ψ (e y)) :
    FixedCommutingProduct.fixedSubgroup β ≃*
      (N ⊓ FixedCommutingProduct.fixedSubgroup ψ : Subgroup D) where
  toFun y := ⟨e y, (e y).2, by
    change ψ (e y) = e y
    rw [← he, show β y = y from y.2]⟩
  invFun x := ⟨e.symm ⟨x, x.2.1⟩, by
    change β (e.symm ⟨x, x.2.1⟩) = e.symm ⟨x, x.2.1⟩
    apply e.injective
    apply Subtype.ext
    rw [he, MulEquiv.apply_symm_apply]
    exact x.2.2⟩
  left_inv y := Subtype.ext (e.symm_apply_apply (y : P))
  right_inv x := Subtype.ext (by
    change ((e (e.symm ⟨x, x.2.1⟩) : N) : D) = x
    rw [MulEquiv.apply_symm_apply])
  map_mul' y y' := Subtype.ext (by
    change ((e ((y : P) * y') : N) : D) = (e y : D) * (e y' : D)
    rw [map_mul]
    rfl)

end FixedInf

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

section Unitary

variable (h : UnitaryFieldData p f K)

theorem toLin_hyp_apply (g : GL (HypIndex r ε) K) (v : HypIndex r ε → K) :
    ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup K (HypIndex r ε → K)) :
      (HypIndex r ε → K) →ₗ[K] (HypIndex r ε → K)) v = (g : Matrix _ _ K) *ᵥ v := by
  rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]

theorem toLin_mem_sesqUnitaryGroup_iff (g : GL (HypIndex r ε) K) :
    Matrix.GeneralLinearGroup.toLin g ∈ sesqUnitaryGroup (hypForm h r ε) ↔
      g ∈ hypUnitary h r ε := by
  rw [mem_sesqUnitaryGroup, mem_hypUnitary, ← gramForm_isometry_iff]
  simp only [toLin_hyp_apply]

@[expose] def hypUnitaryEquiv : hypUnitary h r ε ≃* sesqUnitaryGroup (hypForm h r ε) where
  toFun g := ⟨Matrix.GeneralLinearGroup.toLin (g : GL (HypIndex r ε) K),
    (toLin_mem_sesqUnitaryGroup_iff h _).mpr g.2⟩
  invFun g := ⟨Matrix.GeneralLinearGroup.toLin.symm
      (g : LinearMap.GeneralLinearGroup K (HypIndex r ε → K)),
    (toLin_mem_sesqUnitaryGroup_iff h _).mp (by rw [MulEquiv.apply_symm_apply]; exact g.2)⟩
  left_inv _ := Subtype.ext (MulEquiv.symm_apply_apply _ _)
  right_inv _ := Subtype.ext (MulEquiv.apply_symm_apply _ _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem toLin_scalar (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.toLin (GeneralLinearGroup.scalar (HypIndex r ε) c) :
      LinearMap.GeneralLinearGroup K (HypIndex r ε → K)) :
        Module.End K (HypIndex r ε → K)) = (c : K) • 1 := by
  refine LinearMap.ext fun v => ?_
  rw [toLin_hyp_apply, GeneralLinearGroup.coe_scalar, LinearMap.smul_apply, Module.End.one_apply]
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem eq_scalar_of_toLin (g : GL (HypIndex r ε) K) {c : K} (hc0 : c ≠ 0)
    (hg : ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup K (HypIndex r ε → K)) :
      Module.End K (HypIndex r ε → K)) = c • 1) :
    g = GeneralLinearGroup.scalar (HypIndex r ε) (Units.mk0 c hc0) :=
  eq_scalar_of_mulVec hc0 fun v => by
    have h1 := congrArg (fun φ : Module.End K (HypIndex r ε → K) => φ v) hg
    simp only [LinearMap.smul_apply, Module.End.one_apply] at h1
    rw [← h1, toLin_hyp_apply]

theorem map_normOneScalars_hypUnitaryEquiv :
    (normOneScalars h (hypUnitary h r ε) 0).map (hypUnitaryEquiv h).toMonoidHom =
      sesqNormOneScalars h (hypForm h r ε) := by
  ext z
  constructor
  · rintro ⟨g, ⟨c, hc, -, hg⟩, rfl⟩
    refine ⟨c, hc, ?_⟩
    change ((Matrix.GeneralLinearGroup.toLin (g : GL (HypIndex r ε) K) :
      LinearMap.GeneralLinearGroup K (HypIndex r ε → K)) : Module.End K (HypIndex r ε → K)) = _
    rw [hg, toLin_scalar]
  · rintro ⟨c, hc, hz⟩
    have hc0 := ne_zero_of_norm_eq_one h hc
    refine ⟨(hypUnitaryEquiv h).symm z, ⟨Units.mk0 c hc0, hc, pow_zero _, ?_⟩,
      MulEquiv.apply_symm_apply _ _⟩
    apply eq_scalar_of_toLin _ hc0
    change ((Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm
      (z : LinearMap.GeneralLinearGroup K (HypIndex r ε → K))) :
        LinearMap.GeneralLinearGroup K (HypIndex r ε → K)) :
          Module.End K (HypIndex r ε → K)) = c • 1
    rw [MulEquiv.apply_symm_apply]
    exact hz

@[expose] def hypUnitaryModEquiv : hypUnitaryMod h r ε ≃* sesqProjUnitary h (hypForm h r ε) :=
  QuotientGroup.congr _ _ (hypUnitaryEquiv h) (map_normOneScalars_hypUnitaryEquiv h)

theorem hypUnitaryModEquiv_mk (g : hypUnitary h r ε) :
    hypUnitaryModEquiv h (QuotientGroup.mk g) = QuotientGroup.mk (hypUnitaryEquiv h g) :=
  QuotientGroup.congr_mk _ _ _ _ g

end Unitary

section Special

variable (h : UnitaryFieldData p f K)

theorem toLin_mem_special {g : GL (HypIndex r ε) K} (hg : g ∈ hypSU h r ε) :
    Matrix.GeneralLinearGroup.toLin g ∈ sesqSpecialUnitaryGroup (hypForm h r ε) :=
  (toLin_mem_sesqSpecialUnitaryGroup_iff h _ g).mpr hg

@[expose] def hypSpecialHom : hypSU h r ε →* unitarySpecial (hypForm h r ε) where
  toFun g := ⟨⟨Matrix.GeneralLinearGroup.toLin (g : GL (HypIndex r ε) K),
      sesqSpecialUnitaryGroup_le _ (toLin_mem_special h g.2)⟩,
    Subgroup.mem_subgroupOf.mpr (toLin_mem_special h g.2)⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' _ _ := Subtype.ext (Subtype.ext (map_mul _ _ _))

theorem hypSpecialHom_surjective : Function.Surjective (hypSpecialHom h (r := r) (ε := ε)) := by
  rintro ⟨⟨u, hu⟩, hus⟩
  have hus' : u ∈ sesqSpecialUnitaryGroup (hypForm h r ε) := Subgroup.mem_subgroupOf.mp hus
  refine ⟨⟨Matrix.GeneralLinearGroup.toLin.symm u,
    (toLin_mem_sesqSpecialUnitaryGroup_iff h _ _).mp
      (by rw [MulEquiv.apply_symm_apply]; exact hus')⟩, ?_⟩
  exact Subtype.ext (Subtype.ext (MulEquiv.apply_symm_apply _ _))

abbrev hypProjSpecialHom : hypSU h r ε →* projSpecial h (hypForm h r ε) :=
  (specialProj h _).comp (hypSpecialHom h)

theorem ker_hypProjSpecialHom : (hypProjSpecialHom h (r := r) (ε := ε)).ker = hypScalars h r ε := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_specialProj,
    Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨c, hc, hgc⟩
    have hc0 := ne_zero_of_norm_eq_one h hc
    have hg := eq_scalar_of_toLin (g : GL (HypIndex r ε) K) hc0 hgc
    refine ⟨Units.mk0 c hc0, hc, ?_, hg⟩
    have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.scalar (HypIndex r ε)
        (Units.mk0 c hc0)) : Kˣ) : K) = 1 := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, ← hg]
      exact (mem_hypSU.mp g.2).2
    rw [Matrix.GeneralLinearGroup.det_scalar, card_hypIndex] at h1
    exact Units.ext (h1.trans Units.val_one.symm)
  · rintro ⟨c, hc, -, hg⟩
    refine ⟨c, hc, ?_⟩
    change ((Matrix.GeneralLinearGroup.toLin (g : GL (HypIndex r ε) K) :
      LinearMap.GeneralLinearGroup K (HypIndex r ε → K)) : Module.End K (HypIndex r ε → K)) = _
    rw [hg, toLin_scalar]

theorem hypProjSpecialHom_surjective :
    Function.Surjective (hypProjSpecialHom h (r := r) (ε := ε)) :=
  (specialProj_surjective h _).comp (hypSpecialHom_surjective h)

@[expose] def hypModelEquiv : hypPSU h r ε ≃* projSpecial h (hypForm h r ε) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_hypProjSpecialHom h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (hypProjSpecialHom_surjective h))

theorem hypModelEquiv_hypProj (g : hypSU h r ε) :
    (hypModelEquiv h (hypProj h r ε g) : sesqProjUnitary h (hypForm h r ε)) =
      QuotientGroup.mk ((hypSpecialHom h g : unitarySpecial (hypForm h r ε)) :
        sesqUnitaryGroup (hypForm h r ε)) :=
  rfl

end Special

section Intertwining

variable (h : UnitaryFieldData p f K)

theorem hypModelEquiv_conj (A : hypUnitary h r ε) (g g' : hypSU h r ε)
    (hg' : (g' : GL (HypIndex r ε) K) =
      (A : GL (HypIndex r ε) K) * (g : GL (HypIndex r ε) K) * (A : GL (HypIndex r ε) K)⁻¹) :
    (hypModelEquiv h (hypProj h r ε g') : sesqProjUnitary h (hypForm h r ε)) =
      MulAut.conj (QuotientGroup.mk (hypUnitaryEquiv h A) : sesqProjUnitary h (hypForm h r ε))
        (hypModelEquiv h (hypProj h r ε g)) := by
  rw [hypModelEquiv_hypProj, hypModelEquiv_hypProj, MulAut.conj_apply, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  congr 1
  refine Subtype.ext ?_
  change Matrix.GeneralLinearGroup.toLin (g' : GL (HypIndex r ε) K) =
    Matrix.GeneralLinearGroup.toLin (A : GL (HypIndex r ε) K) *
      Matrix.GeneralLinearGroup.toLin (g : GL (HypIndex r ε) K) *
        (Matrix.GeneralLinearGroup.toLin (A : GL (HypIndex r ε) K))⁻¹
  rw [hg', map_mul, map_mul, map_inv]

theorem semilinearMatrixMap_sq {A : Matrix (HypIndex r ε) (HypIndex r ε) K} {c : K}
    (hAc : A * A.map h.bar = c • 1) (v : HypIndex r ε → K) :
    semilinearMatrixMap h A (semilinearMatrixMap h A v) = c • v := by
  rw [semilinearMatrixMap_apply, semilinearMatrixMap_apply]
  have hbar : (fun i => h.bar ((A *ᵥ fun j => h.bar (v j)) i)) = A.map h.bar *ᵥ v := by
    funext i
    rw [RingHom.map_mulVec]
    congr 1
    funext j
    exact h.bar_bar (v j)
  rw [hbar, mulVec_mulVec, hAc, smul_mulVec, one_mulVec]

theorem semilinearMatrixMap_bijective {A : Matrix (HypIndex r ε) (HypIndex r ε) K} {c : K}
    (hc0 : c ≠ 0) (hAc : A * A.map h.bar = c • 1) :
    Function.Bijective (semilinearMatrixMap h A) := by
  refine ⟨fun v w hvw => ?_, fun w => ⟨semilinearMatrixMap h A (c⁻¹ • w), ?_⟩⟩
  · have h1 := congrArg (semilinearMatrixMap h A) hvw
    rw [semilinearMatrixMap_sq h hAc, semilinearMatrixMap_sq h hAc] at h1
    exact smul_right_injective _ hc0 h1
  · rw [semilinearMatrixMap_sq h hAc, smul_smul, mul_inv_cancel₀ hc0, one_smul]

theorem conj_mulVec_semilinearMatrixMap (A g : GL (HypIndex r ε) K) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = h.bar c) (w : HypIndex r ε → K) :
    ((A * glAut σ g * A⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) w =
      semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K)
        ((g : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w) := by
  have hAA : ((A⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmap : (g : Matrix (HypIndex r ε) (HypIndex r ε) K).map σ =
      (g : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar :=
    Matrix.ext fun i j => hσ _
  rw [semilinearMatrixMap_apply, semilinearMatrixMap_apply, Units.val_mul, Units.val_mul,
    mulVec_mulVec, Matrix.mul_assoc, hAA, Matrix.mul_one, ← mulVec_mulVec, coe_glAut, hmap]
  congr 1
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem unitaryOp_antiConj_apply {V : Type} [AddCommGroup V] [Module K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (τ₀ : V →ₛₗ[h.bar] V) (hτ₀ : Function.Bijective τ₀)
    (hτ₀B : ∀ v w, B (τ₀ v) (τ₀ w) = h.bar (B v w)) (g : sesqUnitaryGroup B) (v : V) :
    unitaryOp (antiConj h τ₀ hτ₀ hτ₀B g) (τ₀ v) = τ₀ (unitaryOp g v) := by
  change (antiEquiv h τ₀ hτ₀) (unitaryOp g ((antiEquiv h τ₀ hτ₀).symm (τ₀ v))) = _
  rw [show τ₀ v = antiEquiv h τ₀ hτ₀ v from rfl, AddEquiv.symm_apply_apply]
  rfl

theorem antiProjConj_mk {V : Type} [AddCommGroup V] [Module K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (τ₀ : V →ₛₗ[h.bar] V) (hτ₀ : Function.Bijective τ₀)
    (hτ₀B : ∀ v w, B (τ₀ v) (τ₀ w) = h.bar (B v w)) (g : sesqUnitaryGroup B) :
    antiProjConj h τ₀ hτ₀ hτ₀B (QuotientGroup.mk g) =
      QuotientGroup.mk (antiConj h τ₀ hτ₀ hτ₀B g) :=
  projConj_mk h _ _ hτ₀B g

theorem hypModelEquiv_antiConj (A : GL (HypIndex r ε) K) {c : K} (hc0 : c ≠ 0)
    (hAc : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = c • 1)
    (hτB : ∀ v w,
      hypForm h r ε (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) v)
        (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) w) =
          h.bar (hypForm h r ε v w))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = h.bar c) (g : hypSU h r ε)
    (hAg : A * glAut σ (g : GL (HypIndex r ε) K) * A⁻¹ ∈ hypSU h r ε) :
    (hypModelEquiv h (hypProj h r ε ⟨_, hAg⟩) : sesqProjUnitary h (hypForm h r ε)) =
      antiProjConj h (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K))
        (semilinearMatrixMap_bijective h hc0 hAc) hτB (hypModelEquiv h (hypProj h r ε g)) := by
  rw [hypModelEquiv_hypProj, hypModelEquiv_hypProj, antiProjConj_mk]
  congr 1
  refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
  obtain ⟨w, rfl⟩ := (semilinearMatrixMap_bijective h hc0 hAc).2 v
  have h1 := unitaryOp_antiConj_apply h _ (semilinearMatrixMap_bijective h hc0 hAc) hτB
    ((hypSpecialHom h g : unitarySpecial (hypForm h r ε)) : sesqUnitaryGroup (hypForm h r ε)) w
  refine Eq.trans ?_ h1.symm
  change ((Matrix.GeneralLinearGroup.toLin (A * glAut σ (g : GL (HypIndex r ε) K) * A⁻¹) :
      LinearMap.GeneralLinearGroup K (HypIndex r ε → K)) : Module.End K (HypIndex r ε → K))
        (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) w) =
    semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K)
      (((Matrix.GeneralLinearGroup.toLin (g : GL (HypIndex r ε) K) :
        LinearMap.GeneralLinearGroup K (HypIndex r ε → K)) : Module.End K (HypIndex r ε → K)) w)
  rw [toLin_hyp_apply, toLin_hyp_apply, conj_mulVec_semilinearMatrixMap h A _ σ hσ w]

end Intertwining

end CFSG.ComponentClassification.CatalogueBUnitaryB
