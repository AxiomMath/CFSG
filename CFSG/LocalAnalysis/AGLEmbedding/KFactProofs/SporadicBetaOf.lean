module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP.Fus

theorem sporadicBetaData_of_card {X : Type} [Group X] {n : ℕ} (hX : Nat.card X = n)
    (hn : n ≠ 0) (hOut : Nat.card (Outer X) ≤ 2)
    (h : ∀ p ∈ n.primeFactors, p ≠ 2 → ¬ p ^ 3 ∣ n ∨ (¬ p ^ 4 ∣ n ∧ HasNoncommPair p X) ∨
      FusionGenerationOf X p) :
    SporadicBetaData X := by
  refine ⟨hOut, fun p hp hp2 => ?_⟩
  rw [hX]
  by_cases hd : p ∣ n
  · exact h p (Nat.mem_primeFactors.2 ⟨hp, hd, hn⟩) hp2
  · exact Or.inl fun h3 => hd ((dvd_pow_self p three_ne_zero).trans h3)

end CFSG.AGLEmbedding
