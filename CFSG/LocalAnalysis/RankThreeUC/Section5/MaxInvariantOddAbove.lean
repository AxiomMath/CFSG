module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.MaxInvariantOdd
import all CFSG.LocalAnalysis.RankThreeUC.Section5.MaxInvariantOdd

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

theorem exists_maxInvariantOdd_ge {G : Type} [Group G] [Finite G] (C B X : Subgroup G)
    (hXC : X ≤ C) (hodd : Odd (Nat.card X))
    (hB : B ≤ Subgroup.normalizer (X : Set G)) :
    ∃ R, R ∈ maxInvariantOdd C B ∧ X ≤ R := by
  obtain ⟨R, hXR, hR⟩ := exists_maximal_ge_of_wellFoundedGT
    ( fun R : Subgroup G => R ≤ C ∧ Odd (Nat.card R) ∧ B ≤ Subgroup.normalizer (R : Set G))
    X ⟨hXC, hodd, hB⟩
  exact ⟨R, hR, hXR⟩

end Section5
end CFSG.LocalAnalysis.RankThreeUC
