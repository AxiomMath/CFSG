module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIILinear
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIISymplectic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIUnitary

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard

theorem classicalHypII_of (hO : OrthogonalHypIIOdd)
    (hC : ClassicalHypIICover) (hM : ClassicalEvenMultiplier) : ClassicalHypII := by
  intro A _ _ hA hT
  by_cases hodd : Odd (Nat.card (center A))
  · obtain ⟨hL | hU' | hS | ⟨n, m, hn, hO' | hO'⟩, h8, -⟩ := hT
    · obtain ⟨n, m, hn, hL⟩ := hL
      exact RankTwoHypIILinear.hypII_of_psl hA hodd hn (ne_four_one_of_psl hL h8) hL
    · obtain ⟨n, m, hn, hU'⟩ := hU'
      by_cases h41 : (n, m) = (4, 1)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h41
        exact hC A hA (Or.inl hU')
      · exact RankTwoHypIIUnitary.hypII_of_psu hA (fun _ => hodd) hn h41 hU'
    · obtain ⟨n, m, -, hS⟩ := hS
      exact RankTwoHypIISymplectic.hypII_of_psp hA hS
    · exact hO A hA hodd n m hn (Or.inl hO')
    · exact hO A hA hodd n m hn (Or.inr hO')
  · rcases hM A hA hT (Nat.not_odd_iff_even.mp hodd) with h | h | h | h
    · exact hC A hA (Or.inl h)
    · exact hC A hA (Or.inr (Or.inl h))
    · exact RankTwoHypIISymplectic.hypII_of_psp hA h
    · exact hC A hA (Or.inr (Or.inr h))

end CFSG.ComponentClassification.RankTwoClassical
