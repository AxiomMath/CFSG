module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.Defs

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.LieType.Steinberg.Adjoint


@[expose] def rootH1 : Fin Tag.D4.rank → ℤ := ![1, 1, 1, 1]

@[expose] def rootH2 : Fin Tag.D4.rank → ℤ := ![1, 1, 2, 1]

@[expose] def frameSet (K : Type) [Field K] : Set ↥(adjointGroup Tag.D4 K) :=
  {g | ∃ β ∈ longOrthRoots, ∃ c : K, g = xPar (rootOperatorFamily Tag.D4) β c ∨
    g = xPar (rootOperatorFamily Tag.D4) (-β) c}

@[expose] def FrameTopRootsMem : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → ∀ B : SL2 K, B ^ 3 = 1 → ∀ c : K,
    xPar (rootOperatorFamily Tag.D4) rootH1 c ∈ Subgroup.closure
        ((fixedSubgroup (gammaP K B) : Set ↥(adjointGroup Tag.D4 K)) ∪ frameSet K) ∧
      xPar (rootOperatorFamily Tag.D4) rootH2 c ∈ Subgroup.closure
        ((fixedSubgroup (gammaP K B) : Set ↥(adjointGroup Tag.D4 K)) ∪ frameSet K)

@[expose] def FrameClosing : Prop :=
  ∀ (K : Type) [Field K] (S : Subgroup ↥(adjointGroup Tag.D4 K)), frameSet K ⊆ S →
    (∀ c : K, xPar (rootOperatorFamily Tag.D4) rootH1 c ∈ S ∧
      xPar (rootOperatorFamily Tag.D4) rootH2 c ∈ S) → S = ⊤

theorem d4GraphA2FrameGen_of (h1 : FrameTopRootsMem) (h2 : FrameClosing) :
    A2Nonsplit.D4GraphA2FrameGen := by
  intro K _ _ hK3 _ B hB3 _
  exact h2 K _ (fun g hg => Subgroup.subset_closure (Or.inr hg)) (h1 K hK3 B hB3)

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen
