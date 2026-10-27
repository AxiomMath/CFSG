module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.G2Pair

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.LieType.Steinberg.Adjoint


@[expose] def D4GraphA2FrameGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 4 ≤ Nat.card K →
    ∀ B : SL2 K, B ^ 3 = 1 → B ≠ 1 →
      Subgroup.closure ((fixedSubgroup (gammaP K B) : Set ↥(adjointGroup Tag.D4 K)) ∪
        {g | ∃ β ∈ longOrthRoots, ∃ c : K, g = xPar (rootOperatorFamily Tag.D4) β c ∨
          g = xPar (rootOperatorFamily Tag.D4) (-β) c}) = ⊤

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
