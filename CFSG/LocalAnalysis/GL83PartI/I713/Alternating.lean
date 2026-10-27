module

public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix

public section

namespace GL83.I713

open CFSG.ComponentClassification.OuterAutomorphisms

theorem card_outer_alternating_le_four {n : ℕ} (hn : 5 ≤ n) :
    Nat.card (Outer (alternatingGroup (Fin n))) ≤ 4 := by
  by_cases h6 : n = 6
  · subst h6
    exact CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.outer_card_le_four
  · have hdvd :=
      CFSG.ComponentClassification.CatalogueSchreierAlternating.outer_card_dvd_two_outside_six
        (n := n) (by omega)
    exact (Nat.le_of_dvd two_pos hdvd).trans (by norm_num)

theorem outClauseFor_alternating {n : ℕ} (hn : 5 ≤ n) :
    OutClauseFor (alternatingGroup (Fin n)) :=
  outClauseFor_of_card_outer_le_four (card_outer_alternating_le_four hn)

end GL83.I713
