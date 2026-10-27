module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses

public section

namespace CFSG.ComponentClassification.RankTwoHypIICover.O8

open Subgroup CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.EvenSmallLie.OmegaEight (omegaT sylowT repTypes repPerm)

@[expose] def O8PairFacts : Prop :=
  ∀ j < 38, repTypes.getD j 0 < 3 → ∀ B ∈ sylowT, B ^ 2 = 1 → B ≠ 1 → B ∉ omegaT →
    B * repPerm j = repPerm j * B → MonoW omegaT false (closure {repPerm j, B})

end CFSG.ComponentClassification.RankTwoHypIICover.O8

end
