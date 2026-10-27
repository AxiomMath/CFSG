module

public import CFSG.LieType.Catalog.Realization
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem simple_and_card_of_lieModel
    (Q : Type) [Group Q] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel Q t n p f) (ht : t ∈ classicalTags) (hp : p = 2 ∨ p = 3) :
    IsSimpleGroup Q ∧ ((t = .PSL → Nat.card Q = ordA (n - 1) (p ^ f)) ∧
      (t = .PSU → Nat.card Q = ordTwistedA (n - 1) (p ^ f)) ∧
      (t = .PSp → Nat.card Q = ordBC n (p ^ f)) ∧
      (t = .POmegaMinus → Nat.card Q = ordTwistedD n (p ^ f))) := by
  obtain ⟨-, -, hs⟩ := CFSG.LieType.Catalog.lieModel_finite_simple Q t n p f h
  have hc : StatedClassicalModel Q t n p f := by
    rcases h with ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, rfl, -⟩
    · exact h
    · exact absurd h (by revert ht; cases t <;> decide)
    · exact absurd h (by revert ht; cases t <;> decide)
    · exact absurd ht (by decide)
  refine ⟨hs, ?_⟩
  rcases hp with rfl | rfl
  · obtain ⟨h1, h2, h3, -, h5⟩ := CFSG.Timmesfeld.card_statedClassicalModel_two hc
    exact ⟨h1, h2, h3, h5⟩
  · obtain ⟨h1, h2, h3, -, -, h6⟩ :=
      CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (by norm_num) hc
    exact ⟨h1, h2, h3, h6⟩

end CFSG.EvenSporadicStandard.M24Std
