module

public import CFSG.GH74.GLS.Balance.PStarDefs

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS

@[expose] noncomputable def OpStar (p : ℕ) {G : Type} [Group G] (X : Subgroup G) : Subgroup G :=
  sSup {N : Subgroup G | N ≤ X ∧ (N.subgroupOf X).Normal ∧ IsPStar p ↥N}

end CFSG.GH74.GLS.Balance
