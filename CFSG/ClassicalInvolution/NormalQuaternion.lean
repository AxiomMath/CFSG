module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.ClassicalInvolution

open Subgroup

@[expose] def NormalQuaternionAt {H : Type*} [Group H] (z : H) : Prop :=
  ∃ K : Subgroup H, K ≤ centralizer ({z} : Set H) ∧
    (K.subgroupOf (centralizer ({z} : Set H))).Normal ∧ z ∈ K ∧
    ∃ (P : Sylow 2 K) (r : ℕ), 3 ≤ r ∧ Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2)))

end CFSG.ClassicalInvolution
