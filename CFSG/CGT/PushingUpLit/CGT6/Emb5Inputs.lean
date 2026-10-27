module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.CGT.PushingUpLit.CGT6

@[expose] def IsZ3E9A4A5 (K : Type) [Group K] : Prop :=
  Nonempty (K ≃* Multiplicative (ZMod 3)) ∨ Nonempty (K ≃* Multiplicative (ZMod 3 × ZMod 3)) ∨
    Nonempty (K ≃* alternatingGroup (Fin 4)) ∨ Nonempty (K ≃* alternatingGroup (Fin 5))

@[expose] def pairGen {L : Type} [Group L] (Y : Subgroup L) (g h : L) : Subgroup L :=
  Subgroup.closure ((Y.map (MulAut.conj g).toMonoidHom : Set L) ∪
    (Y.map (MulAut.conj h).toMonoidHom : Set L))

@[expose] def StellmacherSixOneThree : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ Y : Subgroup S, Nat.card ↥Y = 3 → Subgroup.normalClosure (Y : Set S) = ⊤ →
      (∀ g h : S, IsZ3E9A4A5 ↥(pairGen Y g h)) →
      ∃ n : ℕ, 5 ≤ n ∧ ∃ e : S ≃* alternatingGroup (Fin n), ∃ c : alternatingGroup (Fin n),
        (c : Equiv.Perm (Fin n)).IsThreeCycle ∧ Y.map e.toMonoidHom = Subgroup.zpowers c

end CFSG.CGT.PushingUpLit.CGT6
