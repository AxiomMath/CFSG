module

public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.LieType.Chevalley.ExceptionalCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

variable (τ) in
@[expose] def HasEdgeNeighbor (j : Fin τ.rank) : Prop :=
  ∃ i, τ.cartan i j = -1 ∧ τ.cartan j i = -1

instance (j : Fin τ.rank) : Decidable (HasEdgeNeighbor τ j) := by
  unfold HasEdgeNeighbor
  infer_instance

theorem neighbor_F4 : ∀ j : Fin Tag.F4.rank, HasEdgeNeighbor .F4 j := by
  decide

theorem neighbor_E6 : ∀ j : Fin Tag.E6.rank, HasEdgeNeighbor .E6 j := by
  decide

theorem neighbor_E7 : ∀ j : Fin Tag.E7.rank, HasEdgeNeighbor .E7 j := by
  decide

theorem neighbor_E8 : ∀ j : Fin Tag.E8.rank, HasEdgeNeighbor .E8 j := by
  decide

theorem exists_single_edge (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (j : Fin τ.rank) :
    ∃ i, τ.cartan i j = -1 ∧ τ.cartan j i = -1 := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact neighbor_F4 j
  · exact neighbor_E6 j
  · exact neighbor_E7 j
  · exact neighbor_E8 j

end CFSG.LieType.Chevalley.ExceptionalCover
