module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie

public section

namespace CFSG.Blueprint

open Assembly.LowTwoRank

variable {X : Type} [Group X]

theorem LieModel.card_eq_lieOrd {t : StatedLieTag} {n p f : ℕ} (hn : n ≠ 0)
    (h : LieModel X t n p f) : Nat.card X = EvenSmallLie.CatalogOrders.lieOrd t n (p ^ f) := by
  rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hc
  all_goals exact absurd h0 hn

theorem LieModel.card_psp_three_two (h : LieModel X .PSp 3 2 1) : Nat.card X = 1451520 := by
  rw [h.card_eq_lieOrd (by norm_num)]
  decide

end CFSG.Blueprint
