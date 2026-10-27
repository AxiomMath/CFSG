module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3Even
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourReduce

public section

namespace CFSG.ComponentClassification.RankTwoL3Four

open CFSG.ComponentClassification.RankTwoStandard

theorem rankTwoL3EvenStandard_of
    (h3 : AS76b.Section3Config) (h32 : AS76b.Lemma32) (hB : RankTwoBenderStandard)
    (h4 : L34General) : RankTwoL3EvenStandard := by
  intro G _ _ A hH m hm hL
  have hi : Open.standardComponentOddCore G = ⊥ → m = 2 := fun hO =>
    RankTwoL3Even.l3_first_conjunct_of h3 h32 hB G A hH m hm hL hO
  refine ⟨hi, fun hm2 => ?_, fun hO => ?_⟩
  · subst hm2
    exact h4 G A hH.toNF hL
  · obtain rfl := hi hO
    exact oddCoreFreeConclusion_of_l34Conclusion hO (h4 G A hH.toNF hL)

end CFSG.ComponentClassification.RankTwoL3Four
