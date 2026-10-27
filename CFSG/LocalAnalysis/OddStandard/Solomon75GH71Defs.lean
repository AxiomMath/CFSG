module

public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def HasSylowTwoTypeAhat (G : Type) [Group G] (n : ℕ) : Prop :=
  ∃ (X : Type) (_ : Group X), IsDoubleCoverOfAlt X n ∧
    ∃ (P : Sylow 2 G) (Q : Sylow 2 X), Nonempty (↥P ≃* ↥Q)

end CFSG.OddStandard.Solomon75
