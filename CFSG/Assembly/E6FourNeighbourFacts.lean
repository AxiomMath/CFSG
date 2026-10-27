module

public import CFSG.Assembly.Defs
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Assembly

open Subgroup

@[expose] def E6FourSubcompMark (X : Type*) [Group X] : Prop :=
  LargeEvenMarking X fun lab _ _ _ _ _ =>
    lab.n = 2 ∧ ((lab.tag = .twD ∧ lab.rank = 4) ∨ (lab.tag = .A ∧ lab.rank = 5))

@[expose] def E6FourMark (J : Type*) [Group J] : Prop :=
  LargeEvenMarking J fun lab _ _ _ _ _ => lab.tag = .E6 ∧ lab.n = 2

@[expose] def E6FourInnerFive (J : Type) [Group J] : Prop :=
  ∀ α : MulAut J, α ^ 5 = 1 → α ∈ (MulAut.conj : J →* MulAut J).range

@[expose] def E6FourInnerPerfect (J : Type) [Group J] : Prop :=
  ∀ P : Subgroup (MulAut J), Group.IsPerfect P → P ≤ (MulAut.conj : J →* MulAut J).range

@[expose] def E6FourOutInner : Prop :=
  ∀ (J : Type) [Group J] [Finite J], E6FourMark J → center J = ⊥ →
    E6FourInnerFive J ∧ E6FourInnerPerfect J

@[expose] def E6FourSylowFive : Prop :=
  ∀ (J : Type) [Group J] [Finite J], E6FourMark J → center J = ⊥ →
    ∀ P : Sylow 5 J, Nat.card P = 5 ^ 4

@[expose] def E6FourTwoLocalFive : Prop :=
  ∀ (J : Type) [Group J] [Finite J], E6FourMark J → center J = ⊥ →
    ∃ E U : Subgroup J, CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 4 ∧ U ≠ ⊥ ∧
      IsPGroup 2 U ∧ E ≤ normalizer (U : Set J)

@[expose] def E6FourCentFive : Prop :=
  ∀ (J : Type) [Group J] [Finite J], E6FourMark J → center J = ⊥ →
    ∀ A : Subgroup J, Nat.card A = 5 ^ 4 → ∀ s ∈ A, s ≠ 1 →
      ∀ X : Subgroup J, IsComponentOf X (centralizer ({s} : Set J)) →
        A ≤ normalizer (X : Set J) → A ⊓ centralizer (X : Set J) = zpowers s →
          E6FourSubcompMark X

end CFSG.Assembly

end
