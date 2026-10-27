module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseTwoQuotient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

structure SquareCaseSetting (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G)
    (z : G) : Prop where
  core : CoreSetting G S H
  central : IsCentralInvolution (S : Subgroup G) z
  escape : ¬ Subgroup.centralizer ({z} : Set G) ≤ H
  unique : ∀ z' : G, IsCentralInvolution (S : Subgroup G) z' → z' = z
  square : ∃ v ∈ (S : Subgroup G), v ^ 2 = z
  caseTwo : ∀ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J → escapingBar z ∈ J

@[expose] def SquareCaseRankOneImpossible : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    SquareCaseSetting G S H z → ∀ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J →
      ¬ J ≤ escapingImage H z → (∀ x ∈ J, orderOf x = 2 → x = escapingBar z) → False

@[expose] def SquareCaseHighRankCentralizerImpossible : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    SquareCaseSetting G S H z → ∀ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J →
      ¬ J ≤ escapingImage H z → (∃ x ∈ J, orderOf x = 2 ∧ x ≠ escapingBar z) →
      (∀ c ∈ Subgroup.center J, (c : EscapingQuotient z) = 1 ∨
        (c : EscapingQuotient z) = escapingBar z) →
      (∃ k ∈ escapingSylowImage S z, k ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) ∧
        k ≠ 1 ∧ k ≠ escapingBar z) → False

end CFSG.ProperTwoGeneratedCore.Lemma37
