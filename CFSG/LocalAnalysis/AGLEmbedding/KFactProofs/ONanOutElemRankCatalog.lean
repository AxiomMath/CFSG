module

public import CFSG.RankThree.PartOne.KP.Basic
import CFSG.RankThree.PartOne.TCB.Final
import CFSG.RankThree.PartOne.S11d.SporadicOut
import CFSG.RankThree.PartOne.SPOR.OuterSimple
import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
import CFSG.RankThree.PartTwo.KFacts.KS14Sz
import CFSG.SignalizerFunctorTheorem.CatalogBridge.Cyclic

public section

namespace CFSG.AGLEmbedding.OutElemRank

open CFSG.RankThree.PartOne CFSG.SignalizerFunctorTheorem.CatalogBridge
  CFSG.ComponentClassification.OuterAutomorphisms


theorem elementaryRankAtMostOne_of_catalogGroup {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup S)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpS : ¬ p ∣ Nat.card S) :
    ElementaryRankAtMostOne p (MulAut S) := by
  by_cases h3 : p = 3
  · subst h3
    obtain ⟨f, hf⟩ :=
      RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd S hnab hcat hpS
    exact ElementaryRankAtMostOne.of_isCyclic hp
      (pSubgroupsCyclic_exceptional (Or.inr (Or.inr ⟨2, f, hf⟩)) hp hp2 hpS)
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 h3
  rcases TCB.tauCetiCatalogBridge S hnab hcat |> PlaneCases.catalog_cases with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, ℓ, f, -, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · obtain ⟨a, b, hab⟩ := hnab
    exact absurd (e.injective (by rw [map_mul, map_mul, mul_comm])) hab
  · have hout : Nat.card (Outer S) ≤ 4 :=
      (Nat.card_congr (equivalence e).toEquiv).trans_le (card_outer_alternating_le_four hn)
    exact ElementaryRankAtMostOne.of_outer_card_lt hp hpS (by nlinarith)
  · rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, hch⟩ | ⟨-, ht, hree⟩ | ⟨-, -, hsz⟩
    · exact ElementaryRankAtMostOne.of_isCyclic hp (pSubgroupsCyclic_classical hcl hp hp2 hpS)
    · exact ElementaryRankAtMostOne.of_isCyclic hp
        (pSubgroupsCyclic_exceptional (Or.inl ⟨t, ℓ, f, ht, hch⟩) hp hp2 hpS)
    · exact ElementaryRankAtMostOne.of_isCyclic hp
        (pSubgroupsCyclic_exceptional (Or.inr (Or.inl ⟨t, ℓ, f, ht, hree⟩)) hp hp2 hpS)
    · exact ElementaryRankAtMostOne.of_isCyclic hp
        (pSubgroupsCyclic_exceptional (Or.inr (Or.inr ⟨ℓ, f, hsz⟩)) hp hp2 hpS)
  · rcases sporadicOutSmall_of_simple SPOR.sporadicOuterOrderLeTwoSimple_holds s S hnab ⟨e⟩ with
      hlt | hno
    · exact ElementaryRankAtMostOne.of_outer_card_lt hp hpS (by nlinarith)
    · exact ElementaryRankAtMostOne.of_not_dvd_outer hp hpS (hno p hp hp5)

end CFSG.AGLEmbedding.OutElemRank
