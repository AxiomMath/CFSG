module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenMain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundation

public section

namespace CFSG.ComponentClassification.RankTwoL3Even

open CFSG.ComponentClassification.RankTwoStandard

theorem l3_first_conjunct_of
    (h3 : AS76b.Section3Config) (h32 : AS76b.Lemma32) (hB : RankTwoBenderStandard) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A → ∀ m : ℕ, 2 ≤ m →
      Assembly.LowTwoRank.StatedClassicalModel (rankTwoQuot A) .PSL 3 2 m →
        Open.standardComponentOddCore G = ⊥ → m = 2 :=
  l3_first_conjunct_of_foundation h3 h32 RankTwoFoundation.asc75Theorem4 hB

end CFSG.ComponentClassification.RankTwoL3Even
