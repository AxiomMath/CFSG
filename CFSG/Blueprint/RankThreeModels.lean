module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Blueprint

open Assembly.LowTwoRank

@[expose] def RankThreeIModel (G : Type) [Group G] : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧
    (StatedClassicalModel G .PSU 5 2 f ∨ StatedClassicalModel G .POmegaMinus 4 2 f ∨
      StatedClassicalModel G .PSL 4 2 f ∨ StatedClassicalModel G .PSp 3 2 f)

@[expose] def rankThreeIIClassicalParameters : List (StatedLieTag × ℕ × ℕ) :=
  [(.PSU, 5, 1), (.PSU, 6, 1), (.PSL, 6, 1), (.PSL, 7, 1), (.PSp, 4, 1), (.POmegaPlus, 4, 1),
    (.POmegaMinus, 4, 1), (.PSL, 4, 2), (.PSp, 3, 2), (.PSU, 5, 3)]

@[expose] def RankThreeIIModel (G : Type) [Group G] : Prop :=
  Nonempty (G ≃* NativeSporadic.Co2) ∨ Nonempty (G ≃* NativeSporadic.Th) ∨
    (∃ x ∈ rankThreeIIClassicalParameters, StatedClassicalModel G x.1 x.2.1 2 x.2.2) ∨
    ChevalleyExceptionalModel G .F4 2 1

end CFSG.Blueprint
