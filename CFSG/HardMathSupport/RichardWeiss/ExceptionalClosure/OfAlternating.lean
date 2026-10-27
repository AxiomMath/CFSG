module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Inputs
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open Equiv Equiv.Perm CFSG.CGT.PushingUpLit.CGT6

@[expose] def HasA5Pair {S : Type} [Group S] (Y : Subgroup S) : Prop :=
  ∃ g h : S, Nonempty (↥(pairGen Y g h) ≃* alternatingGroup (Fin 5))

@[expose] def NoA5Branch : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ Y : Subgroup S, Nat.card ↥Y = 3 → Subgroup.normalClosure (Y : Set S) = ⊤ →
      (∀ g h : S, IsZ3E9A4A5 ↥(pairGen Y g h)) → ¬ HasA5Pair Y → False

@[expose] def StellmacherA5 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ Y : Subgroup S, Nat.card ↥Y = 3 → Subgroup.normalClosure (Y : Set S) = ⊤ →
      (∀ g h : S, IsZ3E9A4A5 ↥(pairGen Y g h)) → HasA5Pair Y →
      ∃ n : ℕ, 5 ≤ n ∧ ∃ e : S ≃* alternatingGroup (Fin n), ∃ c : alternatingGroup (Fin n),
        (c : Equiv.Perm (Fin n)).IsThreeCycle ∧ Y.map e.toMonoidHom = Subgroup.zpowers c

theorem stellmacherSixOneThree_of_A5_noA5 (h5 : StellmacherA5) (h0 : NoA5Branch) :
    StellmacherSixOneThree := by
  intro S _ _ hS hnab Y hY hnc hpair
  by_cases hA : HasA5Pair Y
  · exact h5 S hS hnab Y hY hnc hpair hA
  · exact (h0 S hS hnab Y hY hnc hpair hA).elim

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
