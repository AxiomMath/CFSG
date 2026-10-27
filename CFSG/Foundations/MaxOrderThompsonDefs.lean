module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Data.Nat.Lattice

public section

namespace CFSG

open Subgroup

variable {G : Type*} [Group G]

variable (G) in
@[expose] noncomputable def maxAbelianOrder : ℕ :=
  sSup {n : ℕ | ∃ A : Subgroup G, IsMulCommutative A ∧ Nat.card A = n}

variable (G) in
@[expose] def maxOrderAbelianFamily : Set (Subgroup G) :=
  {A | IsMulCommutative A ∧ Nat.card A = maxAbelianOrder G}

variable (G) in
@[expose] def orderThompson : Subgroup G :=
  sSup (maxOrderAbelianFamily G)

variable (G) in
@[expose] def orderZJ : Subgroup G :=
  (center (orderThompson G)).map (orderThompson G).subtype

@[expose] def ambientOrderThompson (S : Subgroup G) : Subgroup G :=
  (orderThompson S).map S.subtype

@[expose] def ambientOrderZJ (S : Subgroup G) : Subgroup G :=
  (orderZJ S).map S.subtype

end CFSG
