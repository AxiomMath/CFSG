module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDefs
public import CFSG.CGT.PushingUpLit.CGT6.Nine7Defs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

structure IsSuzTwoBFour {S : Type} [Group S] (W : Subgroup S) : Prop where
  card : Nat.card W = 4
  mul_self : ∀ w ∈ W, w * w = 1
  card_centralizer : ∀ w ∈ W, w ≠ 1 → Nat.card (centralizer ({w} : Set S)) = 161280
  card_commutator : Nat.card ↥⁅centralizer (W : Set S), centralizer (W : Set S)⁆ = 20160

@[expose] def SuzTwoACentralizerAutExtension : Prop :=
  ∀ {S : Type} [Group S] [Finite S], Blueprint.NativeSporadic.IsSporadic S .Suz →
    ∀ {d : S}, orderOf d = 2 → Nat.card (centralizer ({d} : Set S)) = 3317760 →
      ∀ alpha : MulAut ↥(centralizer ({d} : Set S)),
        ∃ beta : MulAut S, beta d = d ∧
          ∀ x : ↥(centralizer ({d} : Set S)), beta (x : S) = (alpha x : S)

@[expose] def SuzTwoAFusion : Prop :=
  ∀ {S : Type} [Group S] [Finite S], Blueprint.NativeSporadic.IsSporadic S .Suz →
    ∀ W : Subgroup S, IsSuzTwoBFour W →
      ∀ d ∈ ⁅centralizer (W : Set S), centralizer (W : Set S)⁆, orderOf d = 2 →
        Nat.card (centralizer ({d} : Set S)) = 3317760

@[expose] def SuzTwoACentralizerFacts : Prop :=
  ∀ {S : Type} [Group S] [Finite S], Blueprint.NativeSporadic.IsSporadic S .Suz →
    ∀ {d : S}, orderOf d = 2 → Nat.card (centralizer ({d} : Set S)) = 3317760 →
      Group.IsPerfect ↥(centralizer ({d} : Set S)) ∧
        ∀ z ∈ centralizer ({d} : Set S),
          (∀ x ∈ centralizer ({d} : Set S), z * x = x * z) → z = 1 ∨ z = d

@[expose] def SuzTwoBRootRigidity : Prop :=
  ∀ {S : Type} [Group S] [Finite S], Blueprint.NativeSporadic.IsSporadic S .Suz →
    ∀ W : Subgroup S, IsSuzTwoBFour W → ∀ u ∈ W, u ≠ 1 →
      ∀ d ∈ ⁅centralizer (W : Set S), centralizer (W : Set S)⁆, orderOf d = 2 →
        ∀ beta : MulAut S, beta u = u → beta d = d →
          (∀ x ∈ ⁅centralizer (W : Set S), centralizer (W : Set S)⁆, x * d = d * x →
            IsPGroup 2 (zpowers x) → beta x = x ∨ beta x = u * x) →
          ∀ w ∈ W, beta w = w

@[expose] def L34SuzOddZeroStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A V K : Subgroup G) (t y : G) (P : Subgroup G)
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)),
    L34SuzOddSetting A t → L34SuzOddData A V K y →
    P.map (MulAut.conj t).toMonoidHom ≠ P → K = (HarrisLit.swapDiag P t hc).range →
    V ≤ centralizer (P : Set G) → y ∈ centralizer (P : Set G) →
    Odd (Nat.card (center ↥P)) →
    (∀ v ∈ V, v ≠ 1 → P ≤ centralizer ({v} : Set G) ∧
      IsComponent (P.subgroupOf (centralizer ({v} : Set G)))) →
    CGT.PushingUpLit.CGT6.Nine7.Star P

end CFSG.ComponentClassification.GrSLit.L34Sec5S
