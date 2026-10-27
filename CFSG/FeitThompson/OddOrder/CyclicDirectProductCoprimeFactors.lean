module
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.NoncommCoprod

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise Subgroup

variable {W : Type*} [Group W] {A B : Subgroup W}

theorem isCyclic_prod_of_inf_eq_bot [IsCyclic W] (h : A ⊓ B = ⊥) : IsCyclic (↥A × ↥B) := by
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    mul_comm' (A.subtype a) (B.subtype b)
  have hinj : Function.Injective (A.subtype.noncommCoprod B.subtype hcomm) := by
    have hmul := Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr h)
    intro x y hxy
    exact hmul (by simpa [MonoidHom.noncommCoprod_apply] using hxy)
  exact (MulEquiv.isCyclic (MonoidHom.ofInjective hinj)).mpr inferInstance

theorem coprime_natCard_of_inf_eq_bot [Finite W] [IsCyclic W] (h : A ⊓ B = ⊥) :
    (Nat.card A).Coprime (Nat.card B) :=
  have := isCyclic_prod_of_inf_eq_bot h
  coprime_card_of_isCyclic_prod ↥A ↥B

theorem natCard_ne_natCard_of_inf_eq_bot [Finite W] [IsCyclic W] [Nontrivial ↥A]
    (h : A ⊓ B = ⊥) : Nat.card A ≠ Nat.card B := fun hcard =>
  (A.nontrivial_iff_ne_bot.mp ‹_›) (Subgroup.card_eq_one.mp
    (by simpa [Nat.Coprime, ← hcard] using coprime_natCard_of_inf_eq_bot h))

theorem coprime_natCard_and_natCard_ne_of_mul_eq_univ [Finite W] [IsCyclic W]
    [Nontrivial ↥A] [Nontrivial ↥B] (hmul : (A : Set W) * (B : Set W) = Set.univ)
    (hinf : A ⊓ B = ⊥) : (Nat.card A).Coprime (Nat.card B) ∧ Nat.card A ≠ Nat.card B :=
  have hc : A.IsComplement' B :=
    isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf) hmul
  have hinf' : A ⊓ B = ⊥ := disjoint_iff.mp hc.disjoint
  ⟨coprime_natCard_of_inf_eq_bot hinf', natCard_ne_natCard_of_inf_eq_bot hinf'⟩

theorem coprime_natCard_and_natCard_ne_of_isComplement' [Finite W] [IsCyclic W]
    [Nontrivial ↥A] [Nontrivial ↥B] (h : A.IsComplement' B) :
    (Nat.card A).Coprime (Nat.card B) ∧ Nat.card A ≠ Nat.card B :=
  have hinf : A ⊓ B = ⊥ := disjoint_iff.mp h.disjoint
  ⟨coprime_natCard_of_inf_eq_bot hinf, natCard_ne_natCard_of_inf_eq_bot hinf⟩

end CFSG.FeitThompson
