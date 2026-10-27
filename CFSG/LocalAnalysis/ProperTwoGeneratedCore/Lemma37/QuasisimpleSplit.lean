module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Induction

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

@[expose] def TwoPointCyclic {G : Type} [Group G] (H : Subgroup G) (z : G)
    (J : Subgroup (EscapingQuotient z)) : Prop :=
  ∀ j ∈ J, j ∉ escapingImage H z → ∀ P : Subgroup (EscapingQuotient z), IsPGroup 2 P →
    (∀ p ∈ P, p ∈ J ∧ p ∈ escapingImage H z ∧ j⁻¹ * p * j ∈ escapingImage H z) → IsCyclic P

@[expose] def SquareCaseCyclicImpossibleBelow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    CanonicalBelow (Nat.card G) → SquareCaseSetting G S H z →
    ∀ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J → ¬ J ≤ escapingImage H z →
      (∃ x ∈ J, orderOf x = 2 ∧ x ≠ escapingBar z) →
      ((∀ k ∈ escapingSylowImage S z, k ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) →
        k = 1 ∨ k = escapingBar z) ∨
       (∃ c ∈ Subgroup.center J, (c : EscapingQuotient z) ≠ 1 ∧
        (c : EscapingQuotient z) ≠ escapingBar z)) →
      TwoPointCyclic H z J → False

@[expose] def SquareCaseCoverExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    SquareCaseSetting G S H z →
    ∀ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J → ¬ J ≤ escapingImage H z →
      (∃ x ∈ J, orderOf x = 2 ∧ x ≠ escapingBar z) →
      ((∀ k ∈ escapingSylowImage S z, k ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) →
        k = 1 ∨ k = escapingBar z) ∨
       (∃ c ∈ Subgroup.center J, (c : EscapingQuotient z) ≠ 1 ∧
        (c : EscapingQuotient z) ≠ escapingBar z)) →
      (CFSG.BenderSuzuki.IsBenderGroup (J ⧸ Subgroup.center J) ∨
        Nonempty ((J ⧸ Subgroup.center J) ≃* properTwoGenCoreJ1)) → False

@[expose] def SquareCaseSzEightExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    SquareCaseSetting G S H z →
    ∀ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J → ¬ J ≤ escapingImage H z →
      (∃ x ∈ J, orderOf x = 2 ∧ x ≠ escapingBar z) →
      ((∀ k ∈ escapingSylowImage S z, k ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) →
        k = 1 ∨ k = escapingBar z) ∨
       (∃ c ∈ Subgroup.center J, (c : EscapingQuotient z) ≠ 1 ∧
        (c : EscapingQuotient z) ≠ escapingBar z)) →
      Nonempty ((J ⧸ Subgroup.center J) ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) → False

end CFSG.ProperTwoGeneratedCore.Lemma37
