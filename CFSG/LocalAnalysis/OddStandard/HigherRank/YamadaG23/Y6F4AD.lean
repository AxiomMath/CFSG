module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.Blueprint

@[expose] def Y6TargetLie (X : Type) [Group X] : Prop :=
  LieModel X .PSL 2 2 6 ∨ LieModel X .PSU 3 2 3 ∨ LieModel X .PSL 3 2 3

theorem Y6TargetLie.of_mulEquiv {X Z : Type} [Group X] [Group Z] (e : X ≃* Z)
    (h : Y6TargetLie X) : Y6TargetLie Z := by
  rcases h with h | h | h
  · exact Or.inl (LieModel.of_mulEquiv e h)
  · exact Or.inr (Or.inl (LieModel.of_mulEquiv e h))
  · exact Or.inr (Or.inr (LieModel.of_mulEquiv e h))

end CFSG.OddStandard.HigherRank.YamadaG23
