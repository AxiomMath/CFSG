module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def IsTwoSp62 (X : Type) [Group X] : Prop :=
  commutator X = ⊤ ∧ Nat.card (center X) = 2 ∧ LieModel (X ⧸ center X) .PSp 3 2 1

@[expose] def O8Plus2OuterInvolutions : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], LieModel Q .POmegaPlus 4 2 1 →
    ∀ σ : MulAut Q, σ * σ = 1 → (∀ q : Q, σ ≠ MulAut.conj q) →
      4 < Nat.card (fixedSubgroup σ)

end CFSG.EvenSporadicStandard.Co3Std.CentT
