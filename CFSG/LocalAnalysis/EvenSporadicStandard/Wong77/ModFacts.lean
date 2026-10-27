module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.EvenSporadicStandard.Wong77

open Subgroup CFSG.Blueprint.NativeSporadic

@[expose] def permOf (g : Carrier .M23) : Equiv.Perm (Fin 23) :=
  (show M23 from g).1

@[expose] def fixSp {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Carrier .M23 →* (V ≃ₗ[ZMod 2] V)) (a : Carrier .M23) : Submodule (ZMod 2) V :=
  LinearMap.ker ((ρ a : V →ₗ[ZMod 2] V) - LinearMap.id)

structure SylowFacts {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Carrier .M23 →* (V ≃ₗ[ZMod 2] V)) : Prop where
  card_fix : ∀ a : Carrier .M23, orderOf a = 2 → Nat.card (fixSp ρ a) = 2 ^ 7
  card_le : ∀ A : Subgroup (Carrier .M23), (∀ a ∈ A, a * a = 1) → Nat.card A ≤ 2 ^ 4
  distinct : ∀ A : Subgroup (Carrier .M23), (∀ a ∈ A, a * a = 1) → Nat.card A = 2 ^ 4 →
    ∃ a ∈ A, a ≠ 1 ∧ ∃ b ∈ A, b ≠ 1 ∧ fixSp ρ a ≠ fixSp ρ b

end CFSG.EvenSporadicStandard.Wong77
