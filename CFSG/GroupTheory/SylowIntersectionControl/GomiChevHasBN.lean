module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
public import CFSG.GroupTheory.TitsSystem.Basic
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.GH74.BNPair Subgroup

@[expose] def GomiChevHasBN : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsGomiChevTwo X →
    (∃ (t : StatedLieTag) (n f : ℕ), t ≠ .Tits ∧
      CFSG.Blueprint.LieModel (X ⧸ center X) t n 2 f) →
    ∀ Q : Sylow 2 X, ∃ (N : Subgroup X)
      (_ : (cartan (normalizer ((Q : Subgroup X) : Set X)) N).Normal)
      (S : Set (WeylGroup (normalizer ((Q : Subgroup X) : Set X)) N)),
      TitsSystem.IsBNPair (normalizer ((Q : Subgroup X) : Set X)) N S

end CFSG.GroupTheory
