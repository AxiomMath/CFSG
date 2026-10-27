module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlphaData
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP

variable {X : Type} [Group X]

theorem SporadicSmallData.sporadicBetaData (h : SporadicSmallData X) : SporadicBetaData X :=
  ⟨h.1, fun p hp hp2 => (h.2 p hp hp2).imp_right Or.inl⟩

theorem SporadicSmallData.sporadicAlphaData (h : SporadicSmallData X) : SporadicAlphaData X :=
  ⟨h.1, fun p hp hp2 => Or.inl (h.2 p hp hp2)⟩

theorem sporadicSmallData_of_card {n : ℕ} (hX : Nat.card X = n) (hn : n ≠ 0)
    (hOut : Nat.card (Outer X) ≤ 2)
    (h : ∀ p ∈ n.primeFactors, p ≠ 2 → ¬ p ^ 3 ∣ n ∨ (¬ p ^ 4 ∣ n ∧ HasNoncommPair p X)) :
    SporadicSmallData X := by
  refine ⟨hOut, fun p hp hp2 => ?_⟩
  rw [hX]
  by_cases hd : p ∣ n
  · exact h p (Nat.mem_primeFactors.2 ⟨hp, hd, hn⟩) hp2
  · exact Or.inl fun h3 => hd ((dvd_pow_self p three_ne_zero).trans h3)

end CFSG.AGLEmbedding
