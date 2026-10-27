module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

@[expose] def RigidLeviChoiceFor (fam : Family) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A), D.family = fam →
    CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q →
      ∀ p : G, D.IsPrimary p → ∃ W Y : Subgroup G, LeviChoice D p W Y ∧ LeviRigid A p Y

@[expose] def ClassicalRigidChoice : Prop :=
  RigidLeviChoiceFor .linear ∧ RigidLeviChoiceFor .unitary ∧ RigidLeviChoiceFor .orthPlus ∧
    RigidLeviChoiceFor .orthMinus

theorem ClassicalRigidChoice.exists {G : Type} [Group G] [Finite G] (h : ClassicalRigidChoice)
    {A : Subgroup G} (D : ClassicalModel A) (hA : CFSG.Open.IsQuasisimple ↥A)
    (hZ : Odd (Nat.card (center ↥A))) (hq : 4 ≤ D.q) (hfam : D.family ≠ .symplectic) {p : G}
    (hp : D.IsPrimary p) : ∃ W Y : Subgroup G, LeviChoice D p W Y ∧ LeviRigid A p Y := by
  obtain ⟨hL, hU, hP, hM⟩ := h
  cases hD : D.family with
  | linear => exact hL G A D hD hA hZ hq p hp
  | unitary => exact hU G A D hD hA hZ hq p hp
  | symplectic => exact absurd hD hfam
  | orthPlus => exact hP G A D hD hA hZ hq p hp
  | orthMinus => exact hM G A D hD hA hZ hq p hp

end CFSG.ComponentClassification.RankTwoClassical
