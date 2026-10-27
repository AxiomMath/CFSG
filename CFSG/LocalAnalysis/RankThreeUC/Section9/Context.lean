module

public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section9

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC SourceSetting Subgroup

variable {G : Type} [Group G] [Finite G]

def YSet (M : Subgroup G) : Set (Subgroup G) :=
  {Y | Y ≤ M ∧ maxSubgroupsContaining Y ≠ {M} ∧
    ∀ D : Subgroup G, D ≤ Y → Nat.card D = 3 → D ∈ uniqueSet M}

def HSet (M Y : Subgroup G) : Set (Subgroup G) :=
  {H | Y ≤ H ∧ ¬ H ≤ M ∧ CFSG.Open.pRank 3 (normalClosureUnder (oPrimeResidual 3 Y) H) = 1}

def Y2Set (M : Subgroup G) : Set (Subgroup G) :=
  {Y | Y ∈ YSet M ∧ maxSubgroupsContaining Y ≠ {M} ∧
    maxSubgroupsContaining Y ⊆ HSet M Y ∪ {M} ∧
    (∀ A ∈ invariantPPrimeSubgroups M Y 3, ⁅A, oPrimeResidual 3 Y⁆ ≤ pCoreOf 2 A) ∧
    QuotientIsTwoGroup 3 Y}

end Section9

end CFSG.LocalAnalysis.RankThreeUC
