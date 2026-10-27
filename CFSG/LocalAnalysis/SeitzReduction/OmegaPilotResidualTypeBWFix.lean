module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviRead

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem mapsTo_fixSpace_of_normalizes (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q)
    {X : Subgroup (matrixProjectiveDerived Q)}
    (hgX : ∀ x ∈ X, matrixProjectiveConjugationHom Q g x ∈ X) {v : Fin d → K}
    (hv : ∀ x ∈ X, projLift hQ x v = v) :
    ∀ x ∈ X, projLift hQ x (coordinateSemilinearMap g.val v) = coordinateSemilinearMap g.val v :=
  mapsTo_fixedSpace_kappa hQ g (X : Set (matrixProjectiveDerived Q))
    (mapsTo_inv_of_mapsTo _ hgX) hv

theorem mapsTo_relFixSpace_of_core (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q)
    {X : Subgroup (matrixProjectiveDerived Q)}
    (hgX : ∀ x ∈ X, matrixProjectiveConjugationHom Q g x ∈ X) (N₁ N₂ N₃ : Subgroup ↥X)
    (hN : ∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)),
      ∀ M : Subgroup ↥X, M.Normal → IsPGroup 2 M → M ≤ N)
    (hR : IsPGroup 2 ↥(N₁ ⊓ N₂ ⊓ N₃)) (hRn : (N₁ ⊓ N₂ ⊓ N₃).Normal) {v : Fin d → K}
    (hv : ∀ r ∈ N₁ ⊓ N₂ ⊓ N₃, ∀ x ∈ X,
      projLift hQ x (projLift hQ ((r : ↥X) : matrixProjectiveDerived Q) v - v) =
        projLift hQ ((r : ↥X) : matrixProjectiveDerived Q) v - v) :
    ∀ r ∈ N₁ ⊓ N₂ ⊓ N₃, ∀ x ∈ X,
      projLift hQ x (projLift hQ ((r : ↥X) : matrixProjectiveDerived Q)
          (coordinateSemilinearMap g.val v) - coordinateSemilinearMap g.val v) =
        projLift hQ ((r : ↥X) : matrixProjectiveDerived Q) (coordinateSemilinearMap g.val v) -
          coordinateSemilinearMap g.val v := by
  set β := matrixProjectiveConjugationHom Q g with hβ
  have hgX' : ∀ x ∈ X, β⁻¹ x ∈ X := mapsTo_inv_of_mapsTo _ hgX
  set θ := restrictAutOfMapsTo β⁻¹ X hgX' with hθ
  intro r hr x hx
  have hr' := mem_inf_of_isPGroup N₁ N₂ N₃ hN hR hRn θ r hr
  have hβr : β ((θ r : ↥X) : matrixProjectiveDerived Q) = (r : matrixProjectiveDerived Q) := by
    rw [hθ, coe_restrictAutOfMapsTo]
    exact MulAut.apply_inv_self _ _ _
  have e : projLift hQ ((r : ↥X) : matrixProjectiveDerived Q) (coordinateSemilinearMap g.val v) -
      coordinateSemilinearMap g.val v = coordinateSemilinearMap g.val
        (projLift hQ ((θ r : ↥X) : matrixProjectiveDerived Q) v - v) := by
    rw [← hβr, hβ, projLift_kappa_apply, map_sub]
  rw [e]
  exact mapsTo_fixSpace_of_normalizes hQ g hgX (fun y hy => hv _ hr' y hy) x hx

end CFSG.SeitzReduction.OmegaPilot
