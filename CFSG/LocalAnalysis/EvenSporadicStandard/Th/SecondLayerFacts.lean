module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowBounds
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SecondLayer

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L S A B Aa : Subgroup G} {z b : G}

theorem SylowFacts.of_transvCent (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hT : TransvCent L A B Aa)
    (hZ : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B) : SylowFacts L S B Aa :=
  ⟨(W.sylowBounds W2 hT).1, (W.sylowBounds W2 hT).2, hZ⟩

end CFSG.EvenSporadicStandard.ThStd
