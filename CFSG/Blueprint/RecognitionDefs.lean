module

public import CFSG.Models

public noncomputable section

namespace CFSG.Blueprint.Recognition

open Assembly.LowTwoRank NativeSporadic

@[expose] def OddStandardType (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
    Models.OddLieType X ∨ Models.LieModel X .PSL 3 2 2 ∨ IsSporadic X .He

@[expose] def EvenStandardType (X : Type) [Group X] : Prop :=
  Models.EvenLieType X ∨ SporadicRep X

@[expose] def EvenStandardException (X : Type) [Group X] : Prop :=
  Models.LieModel X .PSL 2 2 2 ∨ Models.LieModel X .PSL 3 2 1 ∨
    Models.LieModel X .PSL 4 2 1 ∨ Nonempty (X ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) ∨
    Nonempty (X ≃* StatedProj (StatedSU 3 3 (GaloisField 3 2))) ∨ Models.LieModel X .PSU 4 2 1 ∨
    Models.LieModel X .PSL 3 2 2 ∨ IsSporadic X .He

@[expose] def ResidualA (L : Type) [Group L] : Prop :=
  SporadicRep (L ⧸ Subgroup.center L) ∧ ¬ IsSporadic (L ⧸ Subgroup.center L) .He

@[expose] def ResidualB (L : Type) [Group L] : Prop :=
  Nat.card (Subgroup.center L) = 2 ∧
    (Models.LieModel (L ⧸ Subgroup.center L) .G2 0 2 2 ∨
      Models.LieModel (L ⧸ Subgroup.center L) .F4 0 2 1 ∨
      Models.LieModel (L ⧸ Subgroup.center L) .twistedE6 0 2 1)

@[expose] def ResidualC (L : Type) [Group L] : Prop :=
  Models.LieModel (L ⧸ Subgroup.center L) .PSp 3 2 1 ∨
    Models.LieModel (L ⧸ Subgroup.center L) .PSU 6 2 1 ∨
    Models.LieModel (L ⧸ Subgroup.center L) .POmegaPlus 4 2 1

@[expose] def ResidualD (L : Type) [Group L] : Prop :=
  Subgroup.center L = ⊥ ∧ Models.LieModel L .POmegaMinus 4 2 1

@[expose] def EvenStandardResidual (L : Type) [Group L] : Prop :=
  IsPGroup 2 (Subgroup.center L) ∧ (ResidualA L ∨ ResidualB L ∨ ResidualC L ∨ ResidualD L)

@[expose] def EvenBNRankTwoType (X : Type) [Group X] : Prop :=
  ∃ (t : StatedLieTag) (n f : ℕ), 1 ≤ f ∧
    (t, n) ∈ ({(.PSL, 3), (.PSU, 4), (.PSU, 5), (.PSp, 2), (.G2, 0),
      (.trialityD4, 0), (.twistedF4, 0), (.Tits, 0)} : Set (StatedLieTag × ℕ)) ∧
    Models.LieModel X t n 2 f

@[expose] def EvenSporadicOutcome (X : Type) [Group X] : Prop :=
  IsSporadic X .Co3 ∨ IsSporadic X .HN ∨ IsSporadic X .Fi22 ∨
    IsSporadic X .Fi23 ∨ IsSporadic X .Fi24Prime ∨ IsSporadic X .B ∨ IsSporadic X .M

end CFSG.Blueprint.Recognition
