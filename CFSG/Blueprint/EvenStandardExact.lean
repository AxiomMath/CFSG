module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Blueprint.Recognition.Exact

open Chevalley Assembly.LowTwoRank NativeSporadic

@[expose] def EvenStandardType (X : Type) [Group X] : Prop :=
  EvenLieType X ∨ SporadicRep X

@[expose] def EvenStandardException (X : Type) [Group X] : Prop :=
  LieModel X .PSL 2 2 2 ∨ LieModel X .PSL 3 2 1 ∨ LieModel X .PSL 4 2 1 ∨
    (∃ (K : Type) (_ : Field K) (_ : Fintype K), Fintype.card K = 2 ∧
      Nonempty (X ≃* commutator (Matrix.symplecticGroup (Fin 2) K))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Fintype K), Fintype.card K = 2 ∧
      Nonempty (X ≃* (⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ : Subgroup (ModGL .G2 K)))) ∨
    LieModel X .PSU 4 2 1 ∨ LieModel X .PSL 3 2 2 ∨ IsSporadic X .He

@[expose] def ResidualA (L : Type) [Group L] : Prop :=
  SporadicRep (L ⧸ Subgroup.center L) ∧ ¬ IsSporadic (L ⧸ Subgroup.center L) .He

@[expose] def ResidualB (L : Type) [Group L] : Prop :=
  Nat.card (Subgroup.center L) = 2 ∧
    (LieModel (L ⧸ Subgroup.center L) .G2 0 2 2 ∨ LieModel (L ⧸ Subgroup.center L) .F4 0 2 1 ∨
      LieModel (L ⧸ Subgroup.center L) .twistedE6 0 2 1)

@[expose] def ResidualC (L : Type) [Group L] : Prop :=
  LieModel (L ⧸ Subgroup.center L) .PSp 3 2 1 ∨ LieModel (L ⧸ Subgroup.center L) .PSU 6 2 1 ∨
    LieModel (L ⧸ Subgroup.center L) .POmegaPlus 4 2 1

@[expose] def ResidualD (L : Type) [Group L] : Prop :=
  Subgroup.center L = ⊥ ∧ LieModel L .POmegaMinus 4 2 1

@[expose] def EvenStandardResidual (L : Type) [Group L] : Prop :=
  IsPGroup 2 (Subgroup.center L) ∧ (ResidualA L ∨ ResidualB L ∨ ResidualC L ∨ ResidualD L)

end CFSG.Blueprint.Recognition.Exact
