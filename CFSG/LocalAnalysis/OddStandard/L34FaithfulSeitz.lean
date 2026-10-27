module

public import CFSG.Foundations.Basic
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint

@[expose] def Seitz77Outcome (G : Type) [Group G] (A : Subgroup G) (n f : ℕ) : Prop :=
  (CFSG.oddCore G ⊔ A).Normal ∨
    LieModel ↥(CFSG.layer (G ⧸ center G)) .PSL n 2 (2 * f) ∨
    ∃ (X : Type) (_ : Group X), LieModel X .PSL n 2 f ∧
      Nonempty (↥(CFSG.layer (G ⧸ center G)) ≃* X × X)

end CFSG.OddStandard
