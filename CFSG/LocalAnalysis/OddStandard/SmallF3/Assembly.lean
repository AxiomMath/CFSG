module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Blocks
public import CFSG.LocalAnalysis.OddStandard.SmallF3.EvenCentre
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Balanced
import CFSG.LocalAnalysis.OddStandard.SmallF3.Unbalanced

public section

namespace CFSG.OddStandard.SmallF3

open Subgroup CFSG.Blueprint CFSG.OddStandard.SmallF3Interfaces

theorem assembly
    (hH : ComponentClassification.HarrisLit.Harris82Theorem1SimpleKProperOdd)
    (hCI : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hOdd : ComponentClassification.RankTwoStandard.RankTwoOddLieStandard)
    (hGA : Open.GriessAllModelsStatement)
    (hL33 : SmallF3L33Block) (hU33 : SmallF3U33Block) (hΩ : SmallF3OmegaBlock) :
    SmallF3StandardOddLieU := by
  unfold SmallF3StandardOddLieU
  intro G _ _ _ hnonab hK hU L hL hQ
  have hS : StandardSetting G L := ⟨inferInstance, hnonab, hK, hL⟩
  by_cases hub : ∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥
  · exact oddLieType_of_unbalanced hS hU hQ hub
  · push Not at hub
    have hcentre : OddLieType G ∨
        (center L = ⊥ ∨
          (LieModel (L ⧸ center L) .PSU 4 3 1 ∧ Nat.card (center L) = 2)) := by
      rcases center_eq_bot_or_even_card hS hub with h | hev
      · exact Or.inr (Or.inl h)
      · rcases oddLieType_of_evenCentre hH hGA hS hub hQ hev with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    rcases hcentre with h | hcentre
    · exact h
    · rcases oddLieType_or_cyclic hOdd hCI hS hQ with h | hcyc
      · exact h
      · have hC : SmallF3Cyclic G L :=
          { toStandardSetting := hS, balanced := hub, cyclic := hcyc, centre := hcentre }
        unfold SmallF3LieQuotient at hQ
        rcases hQ with h | h | h | h | h | h | h | h
        · exact hL33 G L hC h
        · exact hU33 G L hC h
        · exact hΩ G L hC (Or.inl h)
        · exact hΩ G L hC (Or.inr (Or.inl h))
        · exact hΩ G L hC (Or.inr (Or.inr (Or.inl h)))
        · exact hΩ G L hC (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact hΩ G L hC (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        · exact hΩ G L hC (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

end CFSG.OddStandard.SmallF3
