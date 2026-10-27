module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCubeFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralDefs

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore


@[expose] def E8NonToralD4Core : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      IsEmpty (LangPlaneData .E8 K E₀) →
      (∀ x ∈ E₀, x ≠ 1 →
        LinearMap.trace (AlgebraicClosure K) (RootModule .E8 (AlgebraicClosure K))
          ((baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) :
            ModGL .E8 (AlgebraicClosure K)) : Module.End (AlgebraicClosure K)
              (RootModule .E8 (AlgebraicClosure K))) ≠ ((-4 : ℤ) : AlgebraicClosure K)) →
      ∀ P : Subgroup (adjointGroup .E8 K), P ≤ E₀ → Nat.card P = 3 ^ 2 →
      ∀ (D : LangPlaneData .E8 K P) (z : adjointGroup .E8 K), z ∈ E₀ → z ∉ P →
      ∀ F : CubeFrame D z, E8KillsSeventyEight F.a → E8D4OrthOrbit F.a F.ω →
        NormalizesRGroup (ringChar K) E₀

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

end
