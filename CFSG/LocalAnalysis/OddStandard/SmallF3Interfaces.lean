module

public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalUnbalanced
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.OddStandard.SmallF3Interfaces

@[expose] def SmallF3LieQuotient (Q : Type) [Group Q] : Prop :=
  CFSG.Blueprint.LieModel Q .PSL 3 3 1 ∨ CFSG.Blueprint.LieModel Q .PSU 3 3 1 ∨
    CFSG.Blueprint.LieModel Q .PSp 2 3 1 ∨ CFSG.Blueprint.LieModel Q .PSL 4 3 1 ∨
    CFSG.Blueprint.LieModel Q .PSU 4 3 1 ∨ CFSG.Blueprint.LieModel Q .POmegaOdd 3 3 1 ∨
    CFSG.Blueprint.LieModel Q .POmegaPlus 4 3 1 ∨ CFSG.Blueprint.LieModel Q .POmegaMinus 4 3 1

@[expose] def UImplication (G : Type) [Group G] : Prop :=
  (∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥) →
    CFSG.ComponentClassification.OutcomeLocal.UOutcome G

@[expose] def SmallF3StandardOddLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ L : Subgroup G, CFSG.Open.standardComponentIsStandard L →
      SmallF3LieQuotient (L ⧸ Subgroup.center L) → CFSG.Blueprint.OddLieType G

@[expose] def SmallF3StandardOddLieU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → UImplication G →
    ∀ L : Subgroup G, CFSG.Open.standardComponentIsStandard L →
      SmallF3LieQuotient (L ⧸ Subgroup.center L) → CFSG.Blueprint.OddLieType G

end CFSG.OddStandard.SmallF3Interfaces
