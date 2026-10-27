module

public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem cartan_odd_column (τ : Tag) (j : Fin τ.rank) :
    ∃ i, i ≠ j ∧ (τ.cartan i j = -1 ∨ τ.cartan i j = -3) := by
  revert j
  cases τ <;> decide

theorem cartan_single_edge_neighbor (τ : Tag)
    (hτ : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (j : Fin τ.rank) :
    ∃ i, i ≠ j ∧ τ.cartan i j = -1 ∧ τ.cartan j i = -1 := by
  have key : ∀ j : Fin τ.rank,
      ∃ i, i ≠ j ∧ (τ.cartan i j, τ.cartan j i) = ((-1 : ℤ), (-1 : ℤ)) := by
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨i, hij, h⟩ := key j
  exact ⟨i, hij, (Prod.mk.inj h).1, (Prod.mk.inj h).2⟩

end CFSG.LieType.Chevalley
