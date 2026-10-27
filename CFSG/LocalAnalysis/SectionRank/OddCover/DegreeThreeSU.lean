module

public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.SectionRank.OddCover

open CFSG.Assembly.LowTwoRank

theorem card_statedSU_three_of_card_eq_sq {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) :
    Nat.card ↥(StatedSU 3 q K) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have hqd : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← Nat.card_eq_fintype_card, hK, pow_two] at hn
    exact ⟨q, hn.symm⟩
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).1 hqd
  subst hf
  exact CFSG.SectionRank.OddCover.card_statedSU_three (p := ringChar K) (f := f) hK

end CFSG.SectionRank.OddCover
