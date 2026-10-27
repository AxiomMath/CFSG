module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.LieType.Universal.Spin.Action
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped Matrix

section SemiSim

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

structure SemiSim (Q : QuadraticForm F V) where
  toFun : V → V
  φ : F ≃+* F
  μ : Fˣ
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul : ∀ (c : F) (x : V), toFun (c • x) = φ c • toFun x
  bijective : Function.Bijective toFun
  map_Q : ∀ x, Q (toFun x) = μ * φ (Q x)

namespace SemiSim

variable {Q : QuadraticForm F V} (g : SemiSim Q)

instance : CoeFun (SemiSim Q) fun _ => V → V := ⟨SemiSim.toFun⟩

theorem map_zero' : g 0 = 0 := by
  have := g.map_add 0 0
  simpa using this

theorem map_neg' (x : V) : g (-x) = -g x := by
  have := g.map_add x (-x)
  rw [add_neg_cancel, g.map_zero'] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

theorem map_sub' (x y : V) : g (x - y) = g x - g y := by
  rw [sub_eq_add_neg, g.map_add, g.map_neg', ← sub_eq_add_neg]

theorem polar_apply (x y : V) : polar Q (g x) (g y) = g.μ * g.φ (polar Q x y) := by
  simp only [QuadraticMap.polar, ← g.map_add, g.map_Q, map_sub, mul_sub]

theorem map_isSingular {u : V} (hu : Q u = 0) : Q (g u) = 0 := by
  rw [g.map_Q, hu, map_zero, mul_zero]

theorem eichler_apply_map {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0) (x : V) :
    eichler Q (g u) (((g.μ : F)⁻¹) • g w) (g x) = g (eichler Q u w x) := by
  have hμ : (g.μ : F) ≠ 0 := g.μ.ne_zero
  have hu' : Q (g u) = 0 := g.map_isSingular hu
  have huw' : polar Q (g u) (((g.μ : F)⁻¹) • g w) = 0 := by
    rw [polar_smul_right, g.polar_apply, huw, map_zero, mul_zero, smul_zero]
  have e1 : polar Q (g x) (g u) • (((g.μ : F)⁻¹) • g w) = g.φ (polar Q x u) • g w := by
    rw [g.polar_apply, smul_smul]
    congr 1
    field_simp
  have e2 : polar Q (g x) (((g.μ : F)⁻¹) • g w) + Q (((g.μ : F)⁻¹) • g w) * polar Q (g x) (g u) =
      g.φ (polar Q x w + Q w * polar Q x u) := by
    rw [polar_smul_right, QuadraticMap.map_smul, g.polar_apply, g.polar_apply, g.map_Q, _root_.map_add,
      _root_.map_mul]
    simp only [smul_eq_mul]
    field_simp
  rw [eichler_apply hu' huw', eichler_apply hu huw, e1, e2, g.map_sub', g.map_add, g.map_smul,
    g.map_smul]

end SemiSim

end SemiSim

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

namespace SemiSim

variable {Q : QuadraticForm F V}

@[expose] def compIso (g : SemiSim Q) (ω : V ≃ₗ[F] V) (hω : ∀ x, Q (ω x) = Q x) : SemiSim Q where
  toFun x := ω (g x)
  φ := g.φ
  μ := g.μ
  map_add x y := by rw [g.map_add, _root_.map_add]
  map_smul c x := by rw [g.map_smul, _root_.map_smul]
  bijective := ω.bijective.comp g.bijective
  map_Q x := by rw [hω, g.map_Q]

theorem compIso_apply (g : SemiSim Q) (ω : V ≃ₗ[F] V) (hω : ∀ x, Q (ω x) = Q x) (x : V) :
    g.compIso ω hω x = ω (g x) := rfl

@[expose] def ofMatrix {ι : Type} [Fintype ι] [DecidableEq ι] (Q : QuadraticForm F (ι → F)) (A : GL ι F)
    (φ : F ≃+* F) (μ : Fˣ)
    (h : ∀ v : ι → F, Q (A.val *ᵥ (fun i => φ (v i))) = μ * φ (Q v)) : SemiSim Q where
  toFun v := A.val *ᵥ (fun i => φ (v i))
  φ := φ
  μ := μ
  map_add x y := by
    have : (fun i => φ ((x + y) i)) = (fun i => φ (x i)) + (fun i => φ (y i)) := by
      funext i
      simp
    rw [this, Matrix.mulVec_add]
  map_smul c x := by
    have : (fun i => φ ((c • x) i)) = φ c • (fun i => φ (x i)) := by
      funext i
      simp
    rw [this, Matrix.mulVec_smul]
  bijective := by
    refine ⟨fun x y hxy => ?_, fun w => ?_⟩
    · have h1 := (Matrix.mulVec_injective_iff_isUnit.mpr A.isUnit) hxy
      funext i
      exact φ.injective (congrFun h1 i)
    · refine ⟨fun i => φ.symm ((A⁻¹.val *ᵥ w) i), ?_⟩
      have : (fun i => φ (φ.symm ((A⁻¹.val *ᵥ w) i))) = A⁻¹.val *ᵥ w := by
        funext i
        simp
      change A.val *ᵥ (fun i => φ (φ.symm ((A⁻¹.val *ᵥ w) i))) = w
      rw [this, Matrix.mulVec_mulVec]
      simp
  map_Q := h

end SemiSim

@[expose] def IsConj {Q : QuadraticForm F V} (α : spinGroup Q ≃* spinGroup Q) (g : SemiSim Q) :
    Prop :=
  ∀ y z, spinAction Q (α y) (g z) = g (spinAction Q y z)

section Conj

variable {Q : QuadraticForm F V} {α : spinGroup Q ≃* spinGroup Q} {g : SemiSim Q}

theorem isConj_ofMatrix {ι : Type} [Fintype ι] [DecidableEq ι] {Q : QuadraticForm F (ι → F)}
    {α : spinGroup Q ≃* spinGroup Q} (A : GL ι F) (φ : F ≃+* F) (μ : Fˣ)
    (h : ∀ v : ι → F, Q (A.val *ᵥ (fun i => φ (v i))) = μ * φ (Q v))
    (hα : ∀ x, spinMatrix Q (α x) =
      A * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv ι φ
        (spinMatrix Q x) * A⁻¹) :
    IsConj α (SemiSim.ofMatrix Q A φ μ h) := by
  intro y z
  change spinAction Q (α y) (A.val *ᵥ (fun i => φ (z i))) =
    A.val *ᵥ (fun i => φ (spinAction Q y z i))
  rw [← spinMatrix_mulVec, ← spinMatrix_mulVec, hα]
  have hφ : (fun i => φ ((((spinMatrix Q y : GL ι F) : Matrix ι ι F) *ᵥ z) i)) =
      (((CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv ι φ
        (spinMatrix Q y) : GL ι F) : Matrix ι ι F) *ᵥ (fun i => φ (z i))) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul,
      CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv_entry]
  have hA : (A⁻¹.val * A.val : Matrix ι ι F) = 1 := Units.inv_mul A
  rw [hφ, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec]
  simp only [Matrix.mul_assoc, hA, Matrix.mul_one, ← Matrix.mulVec_mulVec]

theorem IsConj.conj (h : IsConj α g) (k : spinGroup Q) :
    IsConj (α.trans (MulAut.conj k⁻¹))
      (g.compIso (spinAction Q k⁻¹) (map_spinAction Q k⁻¹)) := by
  intro y z
  have e1 : spinAction Q (k⁻¹ * α y * k) =
      spinAction Q k⁻¹ * spinAction Q (α y) * spinAction Q k := by
    simp only [_root_.map_mul]
  have e2 : ∀ w, spinAction Q k (spinAction Q k⁻¹ w) = w := fun w => by
    rw [← LinearEquiv.mul_apply, ← _root_.map_mul, mul_inv_cancel, _root_.map_one]
    rfl
  rw [SemiSim.compIso_apply, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv, e1,
    LinearEquiv.mul_apply, LinearEquiv.mul_apply, e2, h y z]
  rfl

theorem IsConj.spinAction_eq_eichler (h : IsConj α g) {y : spinGroup Q} {u w : V}
    (hy : spinAction Q y = eichler Q u w) (hu : Q u = 0) (huw : polar Q u w = 0) :
    spinAction Q (α y) = eichler Q (g u) (((g.μ : F)⁻¹) • g w) := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨z, rfl⟩ := g.bijective.2 x
  rw [h y z, hy, g.eichler_apply_map hu huw]

end Conj

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
