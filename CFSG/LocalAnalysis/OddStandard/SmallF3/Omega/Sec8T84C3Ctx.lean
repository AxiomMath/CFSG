module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

structure Ctx (V : Type) [CommGroup V] (u : MulAut V) (H : Subgroup (MulAut V))
    (Bv : Subgroup V) : Prop where
  sq : ∀ v : V, v * v = 1
  card : Nat.card V = 2 ^ 8
  u_sq : u * u = 1
  u_mem : u ∈ H
  fix : ∀ e : V, u e = e ↔ e ∈ Bv
  card_B : Nat.card Bv = 16
  trans : ∀ x ∈ Bv, x ≠ 1 → ∀ y ∈ Bv, y ≠ 1 → ∃ a ∈ H, a x = y

end C10

end CFSG.OddStandard.SmallF3.Omega
