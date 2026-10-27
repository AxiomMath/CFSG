module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SquareCase

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open CFSG.ProperTwoGeneratedCore.Assembly

@[expose] def NoSimpleCentralizerTwoANine : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
    ∀ t : X, orderOf t = 2 →
      Group.IsPerfect (Subgroup.centralizer ({t} : Set X)) →
      Nat.card (Subgroup.center (Subgroup.centralizer ({t} : Set X))) = 2 →
      Nonempty ((Subgroup.centralizer ({t} : Set X)) ⧸
        Subgroup.center (Subgroup.centralizer ({t} : Set X)) ≃* alternatingGroup (Fin 9)) → False

@[expose] def TwoANineCentralizerIsolated : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Sylow 2 X) (t : X),
    IsCentralInvolution (S : Subgroup X) t →
    Group.IsPerfect (EscapingQuotient t) →
    Nat.card (Subgroup.center (EscapingQuotient t)) = 2 →
    Nonempty (EscapingQuotient t ⧸ Subgroup.center (EscapingQuotient t) ≃*
      alternatingGroup (Fin 9)) →
    ∀ g : X, g⁻¹ * t * g ∈ (S : Subgroup X) → g⁻¹ * t * g = t

@[expose] def NoTwoANineQuaternionComponent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    SquareCaseSetting G S H z →
    ∀ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J → ¬ J ≤ escapingImage H z →
      ((∀ k ∈ escapingSylowImage S z, k ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) →
        k = 1 ∨ k = escapingBar z) ∨
       (∃ c ∈ Subgroup.center J, (c : EscapingQuotient z) ≠ 1 ∧
        (c : EscapingQuotient z) ≠ escapingBar z)) →
      Nat.card (Subgroup.center J) = 2 →
      Nonempty ((J ⧸ Subgroup.center J) ≃* alternatingGroup (Fin 9)) → False

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
