module

public import CFSG.GH74.GLS.LU.Local.Transport

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS

structure FiveExtra (G : Type) [Group G] (z : G) (S : Sylow 2 G) : Prop where
  fusion : ∀ x ∈ (S : Subgroup G), orderOf x = 2 → IsConj z x
  model : ∃ (Gs : Type) (_ : Group Gs) (S' : Sylow 2 Gs) (z' : Gs),
    LieModel Gs .PSL 4 5 1 ∧
      (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' ∧ orderOf z' = 2 ∧
      Nonempty (CompatIso G z S z' S')

@[expose] def FiveModelFusion : Prop :=
  ∀ (Gs : Type) [Group Gs], LieModel Gs .PSL 4 5 1 →
    ∀ x y : Gs, orderOf x = 2 → orderOf y = 2 → IsConj x y

end CFSG.GH74.GLS.LU.Local
