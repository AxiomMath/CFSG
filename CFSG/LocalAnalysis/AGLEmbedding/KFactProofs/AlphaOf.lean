module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlphaData

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP

theorem sporadicAlphaData_of_card {X : Type} [Group X] {n : ℕ} (hX : Nat.card X = n)
    (hn : n ≠ 0) (hOut : Nat.card (Outer X) ≤ 2)
    (h : ∀ p ∈ n.primeFactors, p ≠ 2 → ¬ p ^ 3 ∣ n ∨ (¬ p ^ 4 ∣ n ∧ HasNoncommPair p X) ∨
      ModuleDatum X p ∨ AbelianSylowDatum X p ∨ RankLiftDatum X p) :
    SporadicAlphaData X := by
  refine ⟨hOut, fun p hp hp2 => ?_⟩
  rw [hX]
  by_cases hd : p ∣ n
  · rcases h p (Nat.mem_primeFactors.2 ⟨hp, hd, hn⟩) hp2 with h1 | h1 | h1 | h1 | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h1)
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))
  · exact Or.inl (Or.inl fun h3 => hd ((dvd_pow_self p three_ne_zero).trans h3))

end CFSG.AGLEmbedding
