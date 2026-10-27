module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalRealization
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealizationBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryRegular
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix QuadraticMap
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealization
open CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer (mem_matrixDerived_iff)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs
  eq_one_of_kappa_eq_one)

variable {k W : Type} [Field k] [AddCommGroup W] [Module k W] {d : ℕ}
  {Q₀ : QuadraticForm k W} {Qc : QuadraticForm k (Fin d → k)}

@[expose] def transportSemilinear (ψ : Q₀.IsometryEquiv Qc) {φ : k ≃+* k}
    (ρ : W ≃ₛₗ[φ.toRingHom] W) : (Fin d → k) ≃ₛₗ[φ.toRingHom] (Fin d → k) where
  toFun x := ψ (ρ (ψ.symm x))
  invFun x := ψ (ρ.symm (ψ.symm x))
  map_add' x y := by simp only [map_add]
  map_smul' c x := by rw [map_smul, LinearEquiv.map_smulₛₗ, map_smul]
  left_inv x := by
    change ψ (ρ.symm (ψ.symm (ψ (ρ (ψ.symm x))))) = x
    rw [ψ.symm_apply_apply, ρ.symm_apply_apply, ψ.apply_symm_apply]
  right_inv x := by
    change ψ (ρ (ψ.symm (ψ (ρ.symm (ψ.symm x))))) = x
    rw [ψ.symm_apply_apply, ρ.apply_symm_apply, ψ.apply_symm_apply]

theorem transportSemilinear_apply (ψ : Q₀.IsometryEquiv Qc) {φ : k ≃+* k}
    (ρ : W ≃ₛₗ[φ.toRingHom] W) (x : Fin d → k) :
    transportSemilinear ψ ρ x = ψ (ρ (ψ.symm x)) := rfl

theorem transportSemilinear_symm_apply (ψ : Q₀.IsometryEquiv Qc) {φ : k ≃+* k}
    (ρ : W ≃ₛₗ[φ.toRingHom] W) (x : Fin d → k) :
    (transportSemilinear ψ ρ).symm x = ψ (ρ.symm (ψ.symm x)) := rfl

theorem semilinear_eq_id_of_commute_derived [CharP k 2] (ψ : Q₀.IsometryEquiv Qc)
    (hQ : Qc.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule k (Fin d → k), Module.finrank k T = 3 ∧ ∀ x ∈ T, Qc x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Qc, TauCeti.QuadraticMap.orthogonalGroup Qc⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Qc) (hd : 1 ≤ d)
    {φ : k ≃+* k} (ρ : W ≃ₛₗ[φ.toRingHom] W) (hρQ : ∀ w, Q₀ (ρ w) = φ (Q₀ w))
    (hρ : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q₀,
      TauCeti.QuadraticMap.orthogonalGroup Q₀⁆, ∀ w, ρ (g w) = g (ρ w)) :
    φ = 1 ∧ ∀ w, ρ w = w := by
  have hR'Q : ∀ x, Qc (transportSemilinear ψ ρ x) = φ (Qc x) := by
    intro x
    rw [transportSemilinear_apply, ψ.map_app, hρQ, ← ψ.map_app (ψ.symm x), ψ.apply_symm_apply]
  have hgQ : ∀ x, Qc (coordinateSemilinearMap (realizingPair φ (transportSemilinear ψ ρ)) x) =
      (realizingPair φ (transportSemilinear ψ ρ)).right (Qc x) := by
    intro x
    rw [realizingPair_apply, realizingPair_right]
    exact hR'Q x
  have hgmem : realizingPair φ (transportSemilinear ψ ρ) ∈ similarityPairs Qc :=
    ⟨1, fun x => by rw [hgQ, Units.val_one, one_mul]⟩
  have hGΓ : (⟨_, hgmem⟩ : similarityPairs Qc) ∈ unitMultiplierPairs Qc := hgQ
  have hconj : ∀ A : matrixDerived Qc,
      matrixConjugation (realizingPair φ (transportSemilinear ψ ρ)) A.val = A.val := by
    intro A
    apply matrixLinearIso.injective
    apply LinearEquiv.ext
    intro x
    change matrixLinearEquiv (matrixConjugation (realizingPair φ (transportSemilinear ψ ρ))
      A.val) x = matrixLinearEquiv A.val x
    rw [matrixConjugation_vector, realizingPair_addEquiv]
    have hL : matrixLinearEquiv A.val ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Qc,
        TauCeti.QuadraticMap.orthogonalGroup Qc⁆ := (mem_matrixDerived_iff Qc A.val).mp A.2
    have hL₀ : LinearEquiv.autCongr ψ.symm.toLinearEquiv (matrixLinearEquiv A.val) ∈
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q₀, TauCeti.QuadraticMap.orthogonalGroup Q₀⁆ := by
      rw [← derivedOrthogonal_map_isometry ψ.symm]
      exact Subgroup.mem_map_of_mem _ hL
    have hg₀ : ∀ w, LinearEquiv.autCongr ψ.symm.toLinearEquiv (matrixLinearEquiv A.val) w =
        ψ.symm (matrixLinearEquiv A.val (ψ w)) := fun w => by
      rw [LinearEquiv.autCongr_apply]
      rfl
    have h1 := hρ _ hL₀ (ρ.symm (ψ.symm x))
    rw [hg₀, hg₀, LinearEquiv.apply_symm_apply] at h1
    change ψ (ρ (ψ.symm (matrixLinearEquiv A.val (ψ (ρ.symm (ψ.symm x)))))) =
      matrixLinearEquiv A.val x
    rw [h1, ψ.apply_symm_apply, ψ.apply_symm_apply]
  have hκ : matrixProjectiveConjugationHom Qc ⟨_, hgmem⟩ = 1 := by
    apply MulEquiv.ext
    intro x
    obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Qc x
    change matrixProjectiveConjugation Qc ⟨_, hgmem⟩ (matrixProjectiveProjection Qc A) =
      matrixProjectiveProjection Qc A
    rw [matrixProjectiveConjugation_mk]
    congr 1
    apply Subtype.ext
    rw [matrixDerivedConjugation_val, ← matrixConjugation_apply]
    exact hconj A
  have hg1 : realizingPair φ (transportSemilinear ψ ρ) = 1 :=
    congrArg Subtype.val (eq_one_of_kappa_eq_one Qc hQ hT hE hd hGΓ hκ)
  refine ⟨?_, fun w => ?_⟩
  · have h1 := congrArg SemidirectProduct.right hg1
    rwa [realizingPair_right] at h1
  · have h1 : transportSemilinear ψ ρ (ψ w) = ψ w := by
      rw [← realizingPair_apply φ (transportSemilinear ψ ρ), hg1, coordinateSemilinearMap_one]
    rw [transportSemilinear_apply, ψ.symm_apply_apply] at h1
    exact ψ.injective h1

end CFSG.ComponentClassification.UnbalancedCatalog
