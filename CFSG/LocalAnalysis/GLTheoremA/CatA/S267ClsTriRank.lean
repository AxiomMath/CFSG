module

public import CFSG.ClassicalGroups.Orthogonal.OmegaPlusFixedCard
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

@[expose] def D4TriRank : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (Q₈ : QuadraticForm K (Fin 8 → K)),
    Odd (Nat.card K) → ¬ 3 ∣ Nat.card K → CFSG.ClassicalGroups.Orthogonal.IsPlus Q₈ 4 →
    ∀ y : MulAut (matrixProjectiveDerived Q₈), y ^ 3 = 1 → y ∉ matrixProjectiveImage Q₈ →
      ∀ E : Subgroup (matrixProjectiveDerived Q₈),
        E ≤ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y →
        CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
