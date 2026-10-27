module

public import CFSG.LieType.SeitzGeneration.UnitaryHeisB12
public import CFSG.LieType.SeitzGeneration.UnitaryHeis

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank

@[expose] def outerHeisClosure (ℓ f : ℕ) (K : Type) [Field K] (ω α : K) :
    Subgroup (unitarySU ℓ f K 3) :=
  Subgroup.closure {g : unitarySU ℓ f K 3 | ∃ M ∈ outerHeisLines ω α, g ∈ FixU ℓ f K M}

@[expose] def OuterB12AtCard (q : ℕ) : Prop :=
  ∀ (ℓ f : ℕ) (K : Type) [Field K], UnitaryFieldData ℓ f K → ℓ ^ f = q →
    ∀ ω α : K, IsPrimitiveRoot ω 3 → α ^ (ℓ ^ f + 1) = 1 → (¬ ∃ μ : K, μ ^ 3 = α) →
      heisB12 ℓ f K ≤ outerHeisClosure ℓ f K ω α

end CFSG.LieType.SeitzGeneration
