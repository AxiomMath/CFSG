module

public import CFSG.LieType.Seitz.Defs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagTwisted
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagAssembly

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDefs

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree

@[expose] def E6FieldCubes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → Nat.card K ≠ 8 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      ¬ E ≤ e6Inndiag K → seitzHyperGamma 3 E = ⊤

@[expose] def TwE6FieldCubes :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 → q ≠ 2 → q ≠ 8 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      ¬ E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → seitzHyperGamma 3 E = ⊤

@[expose] def E6DiagParCubes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ e6Inndiag K → E6NormalizesR K E → seitzHyperGamma 3 E = ⊤

@[expose] def TwE6DiagParCubes :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → TwE6NormalizesR K σ E →
      seitzHyperGamma 3 E = ⊤

@[expose] def E6DiagNonParCubes :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 → Nat.card K ≠ 4 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ e6Inndiag K → ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) →
      ¬ E6NormalizesR K E → seitzHyperGamma 3 E = ⊤

@[expose] def TwE6DiagNonParCubes :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 → 3 ∣ q + 1 → q ≠ 2 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → ¬ E ≤ twistedE6Inn K σ →
      ¬ TwE6NormalizesR K σ E → seitzHyperGamma 3 E = ⊤

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDefs

end
