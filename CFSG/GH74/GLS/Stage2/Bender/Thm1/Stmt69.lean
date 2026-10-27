module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def Lemma6_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ Y Y₁ : Subgroup G, Y ≤ Op p M → Y ≠ ⊥ → z ∈ normalizer (Y : Set G) → ¬ NF z M Y →
      Y₁ ≤ Op p M ⊓ normalizer (Y : Set G) → Y₁ ≠ ⊥ → ⁅Y₁, zpowers z⁆ = Y₁ → ¬ NF z M Y₁

@[expose] def Lemma6_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ Q X : Subgroup G, MinBad z M p Q X →
      (Nat.card ↥X = p ∧ Inverts z X) ∧
      ¬ NF z M ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ ∧
      ¬ ⁅Q, zpowers z⁆ ≤ normalizer ((⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ : Subgroup G) : Set G) ∧
      ¬ IsMulCommutative ↥Q ∧
      zOf Q ≤ Cen z ∧
      ∀ v ∈ zOf Q, v ≠ 1 → NF z M (zpowers v)

@[expose] def Lemma6_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ Q X : Subgroup G, MinBad z M p Q X → IsExtraspecialPGroup p ↥Q

@[expose] def Lemma6_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ Q X : Subgroup G, MinBad z M p Q X → ⁅Q, zpowers z⁆ = Q

@[expose] def Lemma6_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ Q X : Subgroup G, MinBad z M p Q X → Nat.card ↥Q = p ^ 3 ∧
      ∀ Y : Subgroup G, zOf Q ≤ Y → Y ≤ Q → z ∈ normalizer (Y : Set G) → NF z M Y

@[expose] def Lemma6_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ Q X : Subgroup G, MinBad z M p Q X →
      Op p M = Q ⊔ zOf (Op p M) ∧ IsCyclic ↥(zOf (Op p M)) ∧ zOf (Op p M) ≤ Cen z

@[expose] def Tail6_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ Q : Subgroup G, QP z p (Op p M) Q → IsCyclic ↥(Ep p M) → Ep p M ≤ Cen z →
      IsExtraspecialPGroup p ↥Q → Nat.card ↥Q = p ^ 3 →
      Op p M = Q ⊔ zOf (Op p M) → IsCyclic ↥(zOf (Op p M)) → zOf (Op p M) ≤ Cen z → pRank 2 ↥S = 2

@[expose] def Prop6_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ Q : Subgroup G, QP z p (Op p M) Q →
      (∀ X : Subgroup G, X ≤ Q → X ≠ ⊥ → z ∈ normalizer (X : Set G) → NF z M X) ∨
      (IsCyclic ↥(Ep p M) ∧ Ep p M ≤ Cen z ∧
        (IsExtraspecialPGroup p ↥Q ∧ Nat.card ↥Q = p ^ 3) ∧
        (Op p M = Q ⊔ zOf (Op p M) ∧ IsCyclic ↥(zOf (Op p M)) ∧ zOf (Op p M) ≤ Cen z) ∧
        pRank 2 ↥S = 2 ∧
        ∀ Y : Subgroup G, zOf Q ≤ Y → Y ≤ Q → z ∈ normalizer (Y : Set G) → NF z M Y)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
