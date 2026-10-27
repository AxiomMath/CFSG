module

public import CFSG.LieType.Chevalley.ExceptionalESchreier

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem derivedSeries_outer_eq_bot_of_perm
    (τ : Tag) (K : Type) [Field K] [Finite K] {d : ℕ}
    (hd : derivedSeries (Equiv.Perm (Fin τ.rank)) d = ⊥) :
    derivedSeries (Outer (adjointGroup τ K)) (d + 2) = ⊥ := by
  obtain ⟨-, φ, -, -, -, -, hker⟩ := exceptional_ordinary_intrinsic_simple_pairs τ K
  have h1 := map_derivedSeries_le_derivedSeries φ d
  rw [hd, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
  exact derivedSeries_outer_eq_bot_of_le_ker φ hker h1

theorem exceptional_ordinary_small_rank_Schreier
    (τ : Tag) (K : Type) [Field K] [Finite K] :
    (τ = .G2 → derivedSeries (Outer (adjointGroup τ K)) 3 = ⊥) ∧
      (τ = .F4 ∨ τ = .D4 → derivedSeries (Outer (adjointGroup τ K)) 5 = ⊥) := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    have h2 : Nat.card (Fin Tag.G2.rank) ≤ 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    exact derivedSeries_outer_eq_bot_of_perm Tag.G2 K (derivedSeries_perm_one_eq_bot h2)
  · rintro (rfl | rfl)
    · have h4 : Nat.card (Fin Tag.F4.rank) = 4 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fin]
        rfl
      exact derivedSeries_outer_eq_bot_of_perm Tag.F4 K (derivedSeries_perm_three_eq_bot h4)
    · have h4 : Nat.card (Fin Tag.D4.rank) = 4 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fin]
        rfl
      exact derivedSeries_outer_eq_bot_of_perm Tag.D4 K (derivedSeries_perm_three_eq_bot h4)

end CFSG.LieType.Chevalley
