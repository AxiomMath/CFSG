module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec26Main
public import CFSG.CGT.Timmesfeld75.GoldschmidtMilestone

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.CGT.Timmesfeld75

section Milestone

theorem WData.not_isSylowOf_of_certificates {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {d : Datum A} {V₁ : Subgroup G} (h : Hyp G A) (w : WData d V₁) :
    ¬ IsSylowOf 2 w.S (normalizer (w.W : Set G)) :=
  WData.not_isSylowOf goldschmidt1974_of_milestone h w

end Milestone

end CFSG.OddStandard.Seitz77
