module

public import CFSG.LocalAnalysis.AGLEmbedding.AltSix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms

theorem card_outer_alternatingGroup_dvd_four (n : ℕ) (hn : 5 ≤ n) :
    Nat.card (Outer (alternatingGroup (Fin n))) ∣ 4 := by
  rcases eq_or_ne n 6 with rfl | h6
  · exact card_outer_alternatingGroup_six_dvd_four
  · exact (CFSG.ComponentClassification.CatalogueSchreierAlternating.outer_card_dvd_two_outside_six
      (by omega)).trans (by norm_num)

theorem not_dvd_card_outer_alternatingGroup (n : ℕ) (hn : 5 ≤ n) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (alternatingGroup (Fin n))) := fun h =>
  hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow
    (h.trans ((card_outer_alternatingGroup_dvd_four n hn).trans (by norm_num : 4 ∣ 2 ^ 2)))))

end CFSG.AGLEmbedding
