module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

@[expose] def Step9_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ Q X : Subgroup G, MinBad9 z M p Q X →
      (Nat.card ↥X = p ∧ Inverts z X) ∧
      ¬ NN z p (Op p M) ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ ∧
      ¬ ⁅Q, zpowers z⁆ ≤ normalizer ((⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ : Subgroup G) : Set G) ∧
      ¬ IsMulCommutative ↥Q ∧
      zOf Q ≤ Cen z ∧
      ∀ v ∈ zOf Q, v ≠ 1 → NN z p (Op p M) (zpowers v)

@[expose] def Step9_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ Q X : Subgroup G, MinBad9 z M p Q X → IsExtraspecialPGroup p ↥Q

@[expose] def Step9_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ Q X : Subgroup G, MinBad9 z M p Q X → ⁅Q, zpowers z⁆ = Q

@[expose] def Step9_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ Q X : Subgroup G, MinBad9 z M p Q X → Nat.card ↥Q = p ^ 3 ∧
      ∀ Y : Subgroup G, zOf Q ≤ Y → Y ≤ Q → z ∈ normalizer (Y : Set G) → NN z p (Op p M) Y

@[expose] def Step9_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ Q X : Subgroup G, MinBad9 z M p Q X →
      Op p M = Q ⊔ zOf (Op p M) ∧ IsCyclic ↥(zOf (Op p M)) ∧ zOf (Op p M) ≤ Cen z

end CFSG.GH74.GLS.Stage2.Bender.Thm2
