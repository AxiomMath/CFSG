module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardShape

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.ComponentClassification.HarrisLit

@[expose] def HardBranchInputBalanced : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) →
    ∀ W : Subgroup G, (∀ a ∈ W, a * a = 1) → Nat.card ↥W = 4 →
    ∀ J : Subgroup G, IsTwoComponentIn J (centralizer (W : Set G)) → IsMTypeSchur 3 ↥J →
      ClassBShape ↥J → PartialCentre ↥J → J ⊓ W ≠ ⊥ → ∀ w ∈ J ⊓ W, w ≠ 1 →
        IsTwoComponentIn (ComponentClassification.GSThmB.conjClosure J
          (ComponentClassification.GSThmB.layerIn (centralizer {w}))) (centralizer {w})

theorem hardBranchInput_of_balanced_of_E7 (h : HardBranchBalanced)
    (hGr : CFSG.Open.GriessAllModelsStatement)
    (hE7 : ∀ (Q : Type) [Group Q], CFSG.Blueprint.LieModel Q .E7 0 3 1 →
      CFSG.Models.LieModel Q .E7 0 3 1) : HardBranchInputBalanced := by
  intro G _ _ _ hnab hK hcat hbal W hW2 hW4 J hJ hJM hJs hJp _ w hw hw1
  obtain ⟨n, hn, hmodel⟩ := shape_of_partialCentre_of_E7 hGr hE7 hJs hJp hJM
  exact h G hnab hK hcat hbal W hW2 hW4 J hJ n hn hmodel w hw hw1

end CFSG.OddStandard.HigherRank.F3
