module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.Fin76b.A6X

@[expose] def fixSub {A : Type*} [Group A] (ζ : MulAut A) : Subgroup A where
  carrier := {a | ζ a = a}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := map_one ζ
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

theorem mem_fixSub {A : Type*} [Group A] {ζ : MulAut A} {a : A} : a ∈ fixSub ζ ↔ ζ a = a :=
  Iff.rfl

structure A6AutFacts : Prop where
  fix_invol : ∀ ζ : MulAut (alternatingGroup (Fin 6)), ζ * ζ = 1 → ζ ≠ 1 →
    5 ≤ Nat.card ↥(fixSub ζ)
  sq_A6 : ∀ H : Subgroup (MulAut (alternatingGroup (Fin 6))),
    Nonempty (↥H ≃* alternatingGroup (Fin 6)) →
    ∀ Q : Subgroup (MulAut (alternatingGroup (Fin 6))), Q ≤ H → Nat.card ↥Q = 8 →
      ∀ γ : MulAut (alternatingGroup (Fin 6)), (∀ q ∈ Q, γ * q = q * γ) → γ * γ = 1
  cent_A6 : ∀ H : Subgroup (MulAut (alternatingGroup (Fin 6))),
    Nonempty (↥H ≃* alternatingGroup (Fin 6)) →
    ∀ γ : MulAut (alternatingGroup (Fin 6)), (∀ x ∈ H, γ * x = x * γ) → γ = 1

end CFSG.EvenSporadicStandard.Fin76b.A6X
