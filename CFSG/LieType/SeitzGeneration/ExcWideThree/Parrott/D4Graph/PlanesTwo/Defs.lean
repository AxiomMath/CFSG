module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo.Quad

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph


@[expose] def PairGenTwoG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 → PairGenAt (d4Graph K 1)

@[expose] def QuadGenTwoA2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 → ∀ x : ↥(adjointGroup Tag.D4 K),
    x ^ 3 = 1 → x ≠ 1 → gammaP K (uSL 1 * vSL 1) x = x →
      Subgroup.closure (quadSet x (gammaP K (uSL 1 * vSL 1))) = ⊤

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo
