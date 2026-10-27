module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.Transfer
public import CFSG.LieType.Chevalley.GraphFixedData

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley


@[expose] def TrialityThreeCore : Prop :=
  ∀ (f : ℕ), 1 ≤ f → ∀ (K : Type) [Field K] [Finite K] [CharP K 3], Nat.card K = (3 ^ f) ^ 3 →
    ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ (3 ^ f)) →
      ∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), β ^ 3 = 1 →
        β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →
        DefCharGoodPlus β

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
