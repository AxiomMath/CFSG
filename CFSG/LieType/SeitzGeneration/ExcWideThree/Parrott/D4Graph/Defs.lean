module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Basic
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Families

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP


@[expose] def D4GraphClassOdd : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 5 ≤ ringChar K →
    ∀ α : MulAut ↥(adjointGroup Tag.D4 K), α ^ 3 = 1 →
      (CFSG.LieType.SeitzGeneration.ExcWideThree.D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1) →
        IsG2Type α ∨ IsA2Type α

@[expose] def D4GraphA2PairGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 4 ≤ Nat.card K →
    ∀ B : SL2 K, B ^ 3 = 1 → B ≠ 1 → PairGenAt (gammaP K B)

@[expose] def D4GraphPlanesTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.D4 K) →
      (∀ α ∈ E, α ∉ CFSG.Fischer.innerAut (adjointGroup Tag.D4 K) →
        CFSG.LieType.SeitzGeneration.ExcWideThree.D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1) →
      Subgroup.closure (fixUnion E) = ⊤

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
