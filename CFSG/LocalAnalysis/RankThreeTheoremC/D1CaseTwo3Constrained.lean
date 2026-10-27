module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Comp
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3ConstrainedPrimes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

theorem d1CaseTwo_false_of_constrained {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} (hext : D1Extremal p P M H R) (hcon : HasPrimeConstraint (G := H) p)
    (hgrp : CaseTwoGroupFacts) {L : Type} [Group L] [Finite L] (hiso : IsCaseTwoGroup p L)
    (hdvd : Nat.card L ∣ Nat.card (H ⧸ primeComplementCore (G := H) p)) : False := by
  have hp35 : p = 3 ∨ p = 5 := by
    obtain ⟨d, hd' | hd', -⟩ := hiso
    · exact Or.inl hd'.1
    · exact Or.inr hd'.1
  obtain ⟨-, h7, h41⟩ := hgrp p L hiso
  rcases hp35 with rfl | rfl
  · have h := hext.prime_dvd_card_of_hasPrimeConstraint hcon (by norm_num : Nat.Prime 7)
      ((h7 rfl).trans hdvd)
    omega
  · have h := hext.prime_dvd_card_of_hasPrimeConstraint hcon (by norm_num : Nat.Prime 41)
      ((h41 rfl).trans hdvd)
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC
