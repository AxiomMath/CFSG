module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
import Mathlib.LinearAlgebra.QuadraticForm.Basis

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

private theorem exists_bilin_toQuadraticMap_eq :
    ∃ B : LinearMap.BilinForm K V, B.toQuadraticMap = 0 - Q := by
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (-Q)
  exact ⟨B, by rw [hB, zero_sub]⟩

theorem ι_injective' : Function.Injective (ι Q) := by
  obtain ⟨B, hB⟩ := exists_bilin_toQuadraticMap_eq Q
  intro x y hxy
  have h := congrArg (changeForm hB) hxy
  rw [changeForm_ι, changeForm_ι] at h
  exact (ExteriorAlgebra.ι_inj K x y).mp h

theorem nontrivial_cliffordAlgebra : Nontrivial (CliffordAlgebra Q) := by
  obtain ⟨B, hB⟩ := exists_bilin_toQuadraticMap_eq Q
  exact (changeFormEquiv hB).symm.injective.nontrivial

instance instNontrivialCliffordAlgebra : Nontrivial (CliffordAlgebra Q) :=
  nontrivial_cliffordAlgebra Q

theorem algebraMap_injective' : Function.Injective (algebraMap K (CliffordAlgebra Q)) :=
  (algebraMap K (CliffordAlgebra Q)).injective

theorem isUnit_of_isUnit_ι' {v : V} (h : IsUnit (ι Q v)) : IsUnit (Q v) := by
  refine isUnit_iff_ne_zero.mpr fun hv => ?_
  have h2 := h.mul h
  rw [ι_sq_scalar, hv, map_zero] at h2
  exact not_isUnit_zero h2

theorem isUnit_ι_iff' {v : V} : IsUnit (ι Q v) ↔ IsUnit (Q v) :=
  ⟨isUnit_of_isUnit_ι' Q, isUnit_ι_of_isUnit Q⟩

theorem units_conj_mem_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q) (v : V) :
    (x : CliffordAlgebra Q) * ι Q v * ↑x⁻¹ ∈ LinearMap.range (ι Q) := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction'' generalizing v with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (ι Q a) := by rwa [ha]
    let : Invertible (Q a) := (isUnit_of_isUnit_ι' Q (isUnit_of_invertible (ι Q a))).invertible
    simp_rw [← invOf_units x, ← ha, ι_mul_ι_mul_invOf_ι, LinearMap.mem_range_self]
  | inv_mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (ι Q a) := by rwa [ha]
    let : Invertible (Q a) := (isUnit_of_isUnit_ι' Q (isUnit_of_invertible (ι Q a))).invertible
    simp_rw [← invOf_units x, inv_inv, ← ha, invOf_ι_mul_ι_mul_ι, LinearMap.mem_range_self]
  | one => simp_rw [inv_one, Units.val_one, one_mul, mul_one, LinearMap.mem_range_self]
  | mul y z _ _ hy hz =>
    simp_rw [mul_inv_rev, Units.val_mul]
    suffices ↑y * (↑z * ι Q v * ↑z⁻¹) * ↑y⁻¹ ∈ LinearMap.range (ι Q) by
      simpa only [mul_assoc] using this
    obtain ⟨z', hz'⟩ := hz v
    obtain ⟨y', hy'⟩ := hy z'
    simp_rw [← hz', ← hy', LinearMap.mem_range_self]

theorem conj_mem_range_ι (x : spinGroup Q) (v : V) :
    (x : CliffordAlgebra Q) * ι Q v * ↑x⁻¹ ∈ LinearMap.range (ι Q) :=
  units_conj_mem_range_ι Q (spinGroup.units_mem_lipschitzGroup (x := spinGroup.toUnits x) x.2) v

@[simp]
theorem coe_mul_coe_inv_mul (x : spinGroup Q) (y : CliffordAlgebra Q) :
    (x : CliffordAlgebra Q) * (↑x⁻¹ * y) = y := by
  rw [← mul_assoc, ← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one, one_mul]

@[simp]
theorem coe_inv_mul_coe_mul (x : spinGroup Q) (y : CliffordAlgebra Q) :
    (↑x⁻¹ : CliffordAlgebra Q) * (x * y) = y := by
  rw [← mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one, one_mul]

@[simp]
theorem coe_mul_coe_inv (x : spinGroup Q) : (x : CliffordAlgebra Q) * ↑x⁻¹ = 1 := by
  rw [← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one]

@[simp]
theorem coe_inv_mul_coe (x : spinGroup Q) : (↑x⁻¹ : CliffordAlgebra Q) * x = 1 := by
  rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]

private theorem ι_ofInjective_symm (y : LinearMap.range (ι Q)) :
    ι Q ((LinearEquiv.ofInjective (ι Q) (ι_injective' Q)).symm y) = y := by
  conv_rhs => rw [← (LinearEquiv.ofInjective (ι Q) (ι_injective' Q)).apply_symm_apply y]
  rfl

noncomputable def spinActionLin (x : spinGroup Q) : V →ₗ[K] V :=
  (LinearEquiv.ofInjective (ι Q) (ι_injective' Q)).symm.toLinearMap ∘ₗ
    ((LinearMap.mulLeft K (x : CliffordAlgebra Q) ∘ₗ
      LinearMap.mulRight K ((x⁻¹ : spinGroup Q) : CliffordAlgebra Q) ∘ₗ ι Q).codRestrict
      (LinearMap.range (ι Q)) fun v => by
        simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
          mul_assoc] using conj_mem_range_ι Q x v)

theorem ι_spinActionLin (x : spinGroup Q) (v : V) :
    ι Q (spinActionLin Q x v) = x * ι Q v * ↑x⁻¹ := by
  rw [spinActionLin, LinearMap.comp_apply, LinearEquiv.coe_coe, ι_ofInjective_symm,
    LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, mul_assoc]

noncomputable def spinAction : spinGroup Q →* (V ≃ₗ[K] V) where
  toFun x := LinearEquiv.ofLinearMap (spinActionLin Q x) (spinActionLin Q x⁻¹)
    (LinearMap.ext fun v => ι_injective' Q (by
      rw [LinearMap.comp_apply, LinearMap.id_apply, ι_spinActionLin, ι_spinActionLin, inv_inv]
      simp only [mul_assoc, coe_mul_coe_inv_mul, coe_mul_coe_inv, mul_one]))
    (LinearMap.ext fun v => ι_injective' Q (by
      rw [LinearMap.comp_apply, LinearMap.id_apply, ι_spinActionLin, ι_spinActionLin, inv_inv]
      simp only [mul_assoc, coe_inv_mul_coe_mul, coe_inv_mul_coe, mul_one]))
  map_one' := LinearEquiv.ext fun v => ι_injective' Q (by
    rw [LinearEquiv.coe_ofLinearMap, ι_spinActionLin]
    simp)
  map_mul' x y := LinearEquiv.ext fun v => ι_injective' Q (by
    rw [LinearEquiv.coe_ofLinearMap, LinearEquiv.mul_apply, LinearEquiv.coe_ofLinearMap,
      LinearEquiv.coe_ofLinearMap, ι_spinActionLin, ι_spinActionLin, ι_spinActionLin, mul_inv_rev,
      Submonoid.coe_mul, Submonoid.coe_mul]
    simp only [mul_assoc])

@[simp]
theorem ι_spinAction (x : spinGroup Q) (v : V) :
    ι Q (spinAction Q x v) = x * ι Q v * ↑x⁻¹ :=
  ι_spinActionLin Q x v

theorem spinAction_apply_eq_iff (x : spinGroup Q) (v w : V) :
    spinAction Q x v = w ↔ (x : CliffordAlgebra Q) * ι Q v * ↑x⁻¹ = ι Q w := by
  rw [← ι_spinAction, (ι_injective' Q).eq_iff]

@[simp]
theorem map_spinAction (x : spinGroup Q) (v : V) : Q (spinAction Q x v) = Q v := by
  apply algebraMap_injective' Q
  rw [← ι_sq_scalar, ← ι_sq_scalar, ι_spinAction]
  calc (x : CliffordAlgebra Q) * ι Q v * ↑x⁻¹ * (x * ι Q v * ↑x⁻¹)
      = x * (ι Q v * ι Q v) * ↑x⁻¹ := by simp only [mul_assoc, coe_inv_mul_coe_mul]
    _ = ι Q v * ι Q v := by
      rw [ι_sq_scalar, ← Algebra.commutes, mul_assoc, coe_mul_coe_inv, mul_one]

@[simp]
theorem polar_spinAction (x : spinGroup Q) (v w : V) :
    polar Q (spinAction Q x v) (spinAction Q x w) = polar Q v w := by
  simp only [polar, ← map_add, map_spinAction]

noncomputable def spinToOrthogonalGroup :
    spinGroup Q →* TauCeti.QuadraticMap.orthogonalGroup Q :=
  (spinAction Q).codRestrict _ fun x =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q x)

@[simp]
theorem coe_spinToOrthogonalGroup_apply (x : spinGroup Q) (v : V) :
    ((spinToOrthogonalGroup Q x : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) v =
      spinAction Q x v := by
  rw [spinToOrthogonalGroup, MonoidHom.codRestrict_apply]

theorem commute_of_mem_ker_spinAction {x : spinGroup Q} (hx : x ∈ (spinAction Q).ker)
    (y : CliffordAlgebra Q) : Commute (x : CliffordAlgebra Q) y := by
  have hv : ∀ v, Commute (x : CliffordAlgebra Q) (ι Q v) := fun v => by
    have h : ι Q (spinAction Q x v) = ι Q v := by rw [MonoidHom.mem_ker.mp hx]; rfl
    rw [ι_spinAction] at h
    calc (x : CliffordAlgebra Q) * ι Q v = x * ι Q v * ↑x⁻¹ * x := by
          rw [mul_assoc _ (↑x⁻¹ : CliffordAlgebra Q), coe_inv_mul_coe, mul_one]
      _ = ι Q v * x := by rw [h]
  induction y using CliffordAlgebra.induction with
  | algebraMap r => exact Algebra.commute_algebraMap_right r _
  | ι v => exact hv v
  | mul a b ha hb => exact ha.mul_right hb
  | add a b ha hb => exact ha.add_right hb

theorem ker_spinAction_le_center : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (commute_of_mem_ker_spinAction Q hx g).symm.eq

section Invertible

variable [Invertible (2 : K)]

theorem coe_spinToSpecialOrthogonal_apply' (x : spinGroup Q) (v : V) :
    ((CliffordAlgebra.spinToSpecialOrthogonal Q x :
      TauCeti.QuadraticMap.specialOrthogonalGroup Q) : V ≃ₗ[K] V) v = spinAction Q x v := by
  apply ι_injective' Q
  rw [CliffordAlgebra.coe_spinToSpecialOrthogonal_apply, CliffordAlgebra.ι_spinVectorAction_apply,
    ι_spinAction]
  rfl

theorem spinVectorAction_eq (x : spinGroup Q) : CliffordAlgebra.spinVectorAction Q x =
    spinAction Q x := by
  ext v
  rw [← CliffordAlgebra.coe_spinToSpecialOrthogonal_apply, coe_spinToSpecialOrthogonal_apply']

theorem ker_spinAction_eq :
    (spinAction Q).ker = (CliffordAlgebra.spinToSpecialOrthogonal Q).ker := by
  ext x
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    apply Subtype.ext
    ext v
    rw [coe_spinToSpecialOrthogonal_apply', h]
    rfl
  · intro h
    ext v
    rw [← coe_spinToSpecialOrthogonal_apply', h]
    rfl

theorem mem_ker_spinAction_iff [FiniteDimensional K V] [Nontrivial V] (hQ : Q.Nondegenerate)
    (x : spinGroup Q) :
    x ∈ (spinAction Q).ker ↔ x = 1 ∨ x = spinGroup.negOne Q hQ.ne_zero := by
  rw [ker_spinAction_eq]
  exact CliffordAlgebra.mem_ker_spinToSpecialOrthogonal_iff Q hQ x

end Invertible

section Matrix

open Matrix

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (Q : QuadraticForm K (σ → K))

noncomputable def spinMatrix : spinGroup Q →* GL σ K :=
  (Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (σ → K)).symm.toMonoidHom).comp
    (spinAction Q)

theorem spinMatrix_mulVec (x : spinGroup Q) (v : σ → K) :
    (spinMatrix Q x : Matrix σ σ K) *ᵥ v = spinAction Q x v := by
  have h : Matrix.GeneralLinearGroup.toLin (spinMatrix Q x) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (σ → K)).symm (spinAction Q x) := by
    simp [spinMatrix]
  rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.toLin_apply, h]
  rfl

theorem coe_spinMatrix (x : spinGroup Q) :
    (spinMatrix Q x : Matrix σ σ K) =
      LinearMap.toMatrix' (spinAction Q x : (σ → K) →ₗ[K] σ → K) := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, spinMatrix_mulVec, LinearEquiv.coe_coe]

theorem spinMatrix_mem (x : spinGroup Q) :
    spinMatrix Q x ∈ {A : GL σ K | ∀ v, Q ((A : Matrix σ σ K) *ᵥ v) = Q v} :=
  fun v => by rw [spinMatrix_mulVec, map_spinAction]

theorem range_spinMatrix_le :
    (spinMatrix Q).range ≤
      Subgroup.closure {A : GL σ K | ∀ v, Q ((A : Matrix σ σ K) *ᵥ v) = Q v} := by
  rintro _ ⟨x, rfl⟩
  exact Subgroup.subset_closure (spinMatrix_mem Q x)

end Matrix

end CFSG.LieType.Universal.Spin
