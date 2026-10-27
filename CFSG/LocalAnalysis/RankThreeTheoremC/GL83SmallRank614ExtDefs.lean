module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def IsTwoInvariantIn (B X S : Subgroup G) : Prop :=
  S ≤ X ∧ IsPGroup 2 S ∧ B ≤ normalizer (S : Set G)

@[expose] def IsMaxTwoInvariantIn (B X S : Subgroup G) : Prop :=
  IsTwoInvariantIn B X S ∧ ∀ S' : Subgroup G, IsTwoInvariantIn B X S' → S ≤ S' → S' = S

structure Prop614Pair (M B H S : Subgroup G) : Prop where
  isTwoLocal : IsTwoLocal H
  le : B ≤ H
  not_le : ¬ H ≤ M
  isMax : IsMaxTwoInvariantIn B (H ⊓ M) S
  ne_bot : S ≠ ⊥

@[expose] def Prop614Better (H' S' H S : Subgroup G) : Prop :=
  Nat.card S < Nat.card S' ∨ (Nat.card S = Nat.card S' ∧
    (Nat.card (pCoreOf 2 H) < Nat.card (pCoreOf 2 H') ∨
      (Nat.card (pCoreOf 2 H) = Nat.card (pCoreOf 2 H') ∧ Nat.card H < Nat.card H')))

structure Prop614Extremal (M B H S : Subgroup G) : Prop where
  pair : Prop614Pair M B H S
  max : ∀ H' S' : Subgroup G, Prop614Pair M B H' S' → ¬ Prop614Better H' S' H S

@[expose] def GL83SmallRankProp614Ext (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M → Group.IsSolvable M →
    Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) →
    ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
      ∀ H S : Subgroup G, Prop614Extremal M (zpowers x ⊔ zpowers z) H S →
        ¬ 3 ∣ (zpowers x ⊔ zpowers z).relIndex H →
        H = normalizer (pCoreOf 2 H : Set G) →
        IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) H S →
        pCoreOf 2 H ≤ S →
        (∀ S₀ : Subgroup G, pCoreOf 2 H < S₀ → S₀ ≤ S →
          S ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (S₀ : Set G) →
          normalizer (S₀ : Set G) ≤ M) →
        (∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
          normalizer (S₀ : Set G) ≤ M) → False

end CFSG.LocalAnalysis.RankThreeTheoremC
