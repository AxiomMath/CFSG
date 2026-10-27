module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj

public section

namespace CFSG.ClassicalInvolution.PhanP

open QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts

variable {F : Type} [Field F] [Invertible (2 : F)] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

@[expose] noncomputable def rangeIsometry {E : Type} [AddCommGroup E] [Module F E]
    {QE : QuadraticForm F E} (α β : QE →qᵢ Q) (hα : Function.Injective α)
    (hβ : Function.Injective β) :
    (Q.restrict (LinearMap.range α.toLinearMap)).IsometryEquiv
      (Q.restrict (LinearMap.range β.toLinearMap)) where
  toLinearEquiv := (LinearEquiv.ofInjective α.toLinearMap hα).symm.trans
    (LinearEquiv.ofInjective β.toLinearMap hβ)
  map_app' x := by
    obtain ⟨e, rfl⟩ := (LinearEquiv.ofInjective α.toLinearMap hα).surjective x
    change Q ((((LinearEquiv.ofInjective α.toLinearMap hα).symm.trans
      (LinearEquiv.ofInjective β.toLinearMap hβ)) (LinearEquiv.ofInjective α.toLinearMap hα e) :
        LinearMap.range β.toLinearMap) : V) =
      Q ((LinearEquiv.ofInjective α.toLinearMap hα e : LinearMap.range α.toLinearMap) : V)
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    change Q (β e) = Q (α e)
    rw [β.map_app, α.map_app]

omit [Invertible (2 : F)] [FiniteDimensional F V] in
theorem rangeIsometry_apply {E : Type} [AddCommGroup E] [Module F E] {QE : QuadraticForm F E}
    (α β : QE →qᵢ Q) (hα : Function.Injective α) (hβ : Function.Injective β) (e : E) :
    ((rangeIsometry α β hα hβ ⟨α e, e, rfl⟩ : LinearMap.range β.toLinearMap) : V) = β e := by
  change (((LinearEquiv.ofInjective α.toLinearMap hα).symm.trans
    (LinearEquiv.ofInjective β.toLinearMap hβ)) ⟨α e, e, rfl⟩ : V) = β e
  have : (⟨α e, e, rfl⟩ : LinearMap.range α.toLinearMap) =
      LinearEquiv.ofInjective α.toLinearMap hα e := rfl
  rw [this, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

@[expose] noncomputable def isometryEquivRange {E : Type} [AddCommGroup E] [Module F E]
    {QE : QuadraticForm F E} (α : QE →qᵢ Q) (hα : Function.Injective α) :
    QE.IsometryEquiv (Q.restrict (LinearMap.range α.toLinearMap)) where
  toLinearEquiv := LinearEquiv.ofInjective α.toLinearMap hα
  map_app' e := α.map_app e

omit [Invertible (2 : F)] [FiniteDimensional F V] in
theorem nondegenerate_range {E : Type} [AddCommGroup E] [Module F E] {QE : QuadraticForm F E}
    (α : QE →qᵢ Q) (hα : Function.Injective α) (hQE : QE.Nondegenerate) :
    (Q.restrict (LinearMap.range α.toLinearMap)).Nondegenerate :=
  (isometryEquivRange α hα).nondegenerate_iff.mp hQE

theorem exists_spin_extend [Finite F] (hodd : Odd (Nat.card F)) [Nontrivial V]
    (hQ : (polarBilin Q).Nondegenerate) {E : Type} [AddCommGroup E] [Module F E]
    {QE : QuadraticForm F E} (α β : QE →qᵢ Q) (hα : Function.Injective α)
    (hβ : Function.Injective β) (hreg : (Q.restrict (LinearMap.range α.toLinearMap)).Nondegenerate)
    (hdim : 2 ≤ Module.finrank F (LinearMap.BilinForm.orthogonal Q.polarBilin
      (LinearMap.range α.toLinearMap))) :
    ∃ y : spinGroup Q, ∀ e, spinAction Q y (α e) = β e := by
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  set W := LinearMap.range α.toLinearMap with hW
  obtain ⟨Θ, hΘ⟩ := (rangeIsometry α β hα hβ).exists_extension hreg
  let g : TauCeti.QuadraticMap.orthogonalGroup Q :=
    ⟨Θ.toLinearEquiv, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => Θ.map_app x⟩
  have hWP : ∀ x ∈ W, ∀ y ∈ LinearMap.BilinForm.orthogonal Q.polarBilin W, polar Q y x = 0 := by
    intro x hx y hy
    have h1 : Q.polarBilin x y = 0 := hy x hx
    rw [QuadraticMap.polarBilin_apply_apply] at h1
    rw [QuadraticMap.polar_comm]
    exact h1
  have hP := hQnd.nondegenerate_restrict_orthogonal hreg
  obtain ⟨h, hhfix, hhdet, hhsn⟩ := exists_reflection_correction hodd hQnd hWP hP hdim g
  set g' : TauCeti.QuadraticMap.orthogonalGroup Q := g * h with hg'
  have hd : QuadraticMap.orthogonalDet Q g' = 1 := by
    rw [hg', map_mul, hhdet, ← pow_two]
    exact TauCeti.QuadraticMap.orthogonalDet_sq hQ.1 g
  have hs : CliffordAlgebra.orthogonalSpinorNorm Q hQnd g' = 1 := by
    rw [hg', map_mul, hhsn]
    exact mul_inv_cancel _
  obtain ⟨y, hy⟩ := exists_spinAction_eq hQnd g' hd hs
  refine ⟨y, fun e => ?_⟩
  have hfix : (h : V ≃ₗ[F] V) (α e) = α e := hhfix _ ⟨e, rfl⟩
  rw [hy, hg', Subgroup.coe_mul, LinearEquiv.mul_apply, hfix]
  have := hΘ ⟨α e, e, rfl⟩
  rw [rangeIsometry_apply α β hα hβ e] at this
  exact this

end CFSG.ClassicalInvolution.PhanP
