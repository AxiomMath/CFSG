module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Defs
public import CFSG.Milestones.ASVolI.I3

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ASVolI.ChIJK

@[expose] def POmegaPlusCentreExpTwo : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → ∀ n : ℕ, (n = 4 ∨ n = 6) →
    CFSG.Blueprint.LieModel (K ⧸ center K) .POmegaPlus n 3 1 → ∀ x ∈ center K, x * x = 1

@[expose] def LinUnitInvolutionComponents : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup Y] (p n r : ℕ), p.Prime → p ≠ 2 →
    (CFSG.Blueprint.LieModel Y .PSL n p r ∨ CFSG.Blueprint.LieModel Y .PSU n p r) →
    ∀ v : Y, orderOf v = 2 → ∀ C : Subgroup Y, IsComponentIn C (centralizer {v}) →
      ∃ k s : ℕ, CFSG.Blueprint.LieModel (↥C ⧸ center ↥C) .PSL k p s ∨
        CFSG.Blueprint.LieModel (↥C ⧸ center ↥C) .PSU k p s

@[expose] def POmegaPlusNotLinUnit : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (n k s : ℕ), (n = 4 ∨ n = 6) →
    CFSG.Blueprint.LieModel Q .POmegaPlus n 3 1 →
      ¬ CFSG.Blueprint.LieModel Q .PSL k 3 s ∧ ¬ CFSG.Blueprint.LieModel Q .PSU k 3 s

@[expose] def HardBranchBalanced : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) →
    ∀ W : Subgroup G, (∀ a ∈ W, a * a = 1) → Nat.card ↥W = 4 →
    ∀ J : Subgroup G,
      ComponentClassification.HarrisLit.IsTwoComponentIn J (centralizer (W : Set G)) →
      ∀ n : ℕ, (n = 4 ∨ n = 6) →
        CFSG.Blueprint.LieModel (↥J ⧸ Open.fusionZStar ↥J) .POmegaPlus n 3 1 →
      ∀ w ∈ J ⊓ W, w ≠ 1 →
        ComponentClassification.HarrisLit.IsTwoComponentIn
          (ComponentClassification.GSThmB.conjClosure J
            (ComponentClassification.GSThmB.layerIn (centralizer {w}))) (centralizer {w})

end CFSG.OddStandard.HigherRank.F3
