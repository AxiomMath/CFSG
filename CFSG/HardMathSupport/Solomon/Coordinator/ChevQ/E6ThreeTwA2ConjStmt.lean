module

public import CFSG.LieType.Chevalley.TwistedE6NormalForm

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def TwE6ThreeA2ConjStmt :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 → 3 ∣ q + 1 → q ≠ 2 →
    ∀ x ∈ twistedE6RootGroup K σ, ∀ y ∈ twistedE6RootGroup K σ, x ^ 3 = 1 → y ^ 3 = 1 →
      Module.finrank K
          (LinearMap.ker ((x : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24 →
      Module.finrank K
          (LinearMap.ker ((y : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24 →
      ∃ g ∈ twistedE6RootGroup K σ, g * x * g⁻¹ = y

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
