module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviRead

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem map_coordinateSemilinearMap_eq_zero (g : similarityPairs Q) {v : Fin d → K}
    (hv : Q v = 0) : Q (coordinateSemilinearMap g.val v) = 0 := by
  obtain ⟨μ, hμ⟩ := g.2
  rw [hμ, hv, map_zero, mul_zero]

variable [Finite K] [CharP K 2]

theorem spLeviSection_of_trace_restrict_add (hQ : ∃ v, Q v ≠ 0)
    (fp : MulAut (matrixProjectiveDerived Q) →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs Q, fp (matrixProjectiveConjugationHom Q g) = g.val.right)
    (hsurj : ∀ β : MulAut (matrixProjectiveDerived Q),
      ∃ g, matrixProjectiveConjugationHom Q g = β)
    {X : Subgroup (matrixProjectiveDerived Q)} (U : Submodule K (Fin d → K))
    (hXU : ∀ x ∈ X, ∀ u ∈ U, projLift hQ x u ∈ U)
    (hTU : ∀ g : similarityPairs Q, (∀ x ∈ X, matrixProjectiveConjugationHom Q g x ∈ X) →
      ∀ u ∈ U, coordinateSemilinearMap g.val u ∈ U)
    (c : K) (hc : ∀ σ : K ≃+* K, σ c = c)
    {r : ℕ} (hr : 1 ≤ r) (ρ : ↥X →* StatedSp r K) (hρ : Function.Surjective ρ)
    (htr : ∀ x : ↥X, spMatTrace (ρ x) + c = LinearMap.trace K U
      (((projLift hQ (x : matrixProjectiveDerived Q) : (Fin d → K) →ₗ[K] (Fin d → K))).restrict
        (hXU x x.2))) :
    SpLeviSection fp X ρ.ker := by
  refine spLeviSection_of_hom fp hr ρ hρ fun β hβ _ x => ?_
  obtain ⟨g, rfl⟩ := hsurj β
  have hβ' := mapsTo_inv_of_mapsTo _ hβ
  have hTU' : ∀ u ∈ U, (coordinateSemilinearMap g.val).symm u ∈ U := by
    intro u hu
    have h := hTU g⁻¹ (by rw [map_inv]; exact hβ') u hu
    rwa [Subgroup.coe_inv, coordinateSemilinearMap_inv] at h
  have h1 := htr (restrictAutOfMapsTo (matrixProjectiveConjugationHom Q g) X hβ x)
  have h2 := htr x
  have h3 := trace_restrict_projLift_kappa hQ g U (hTU g hβ) hTU' x (hXU x x.2)
    (hXU _ (restrictAutOfMapsTo (matrixProjectiveConjugationHom Q g) X hβ x).2)
  rw [hfp]
  have h4 : spMatTrace (ρ (restrictAutOfMapsTo (matrixProjectiveConjugationHom Q g) X hβ x)) + c =
      g.val.right (spMatTrace (ρ x) + c) := by
    rw [h1, h2]
    exact h3
  rw [map_add, hc] at h4
  exact add_right_cancel h4

end CFSG.SeitzReduction.OmegaPilot
