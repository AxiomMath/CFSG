module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalUnbalanced
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def RankTwoHeStandard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G),
    ComponentClassification.RankTwoStandard.RankTwoHyp G A →
    ¬ IsSporadic (ComponentClassification.RankTwoStandard.rankTwoQuot A) .He

@[expose] def KProperSimpleUnbalancedUOutcome : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper Blueprint.Catalog G →
    (∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥) →
    ComponentClassification.OutcomeLocal.UOutcome G

@[expose] def HeStandardBalanced : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper Blueprint.Catalog G →
    ¬ ComponentClassification.OutcomeLocal.UOutcome G →
    (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) →
    ∀ L : Subgroup G, standardComponentIsStandard L → IsSporadic (L ⧸ center L) .He →
      center L = ⊥ → ¬ 2 ≤ Open.pRank 2 (centralizer (L : Set G)) → False

end CFSG.OddStandard
