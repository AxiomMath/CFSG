module

public import CFSG.LocalAnalysis.OddStandard.ChildHe
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHeCheck
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFlat

public section

namespace CFSG.OddStandard

open CFSG.ComponentClassification

theorem rankTwoHeStandard_of_lemmas
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) : RankTwoHeStandard :=
  fun _ _ _ _ hA => RankTwoSporadic.He.not_isSporadic_He_of_lemmas h32 h33 hA

theorem rankTwoHeStandard_of_flat
    (hflat : Asc76.Sec4.Thm5Flat) : RankTwoHeStandard :=
  rankTwoHeStandard_of_lemmas (RankTwoFoundation.lemma32_of_flat hflat)
    (RankTwoFoundation.lemma33Three_of_flat hflat)

end CFSG.OddStandard
