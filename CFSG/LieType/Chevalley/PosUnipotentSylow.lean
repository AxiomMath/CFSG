module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.ChevalleySplitBN

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique

variable {K : Type} [Field K]

theorem isSylowTwoOf_posUnipotent
    [Finite K] [CharP K 2] (τ : Tag) :
    IsSylowTwoOf (posUnipotent τ K) (adjointGroup τ K) := by
  have hUC : posUnipotent τ K ≤ adjointGroup τ K :=
    posUnipotent_le_adjointGroup (τ := τ) (K := K)
  obtain ⟨hP, hIdx⟩ := isPGroup_and_not_dvd_index (τ := τ) (K := K) 2 hUC
    (card_posUnipotent (τ := τ) (K := K))
  exact ⟨hUC, hP.of_equiv (Subgroup.subgroupOfEquivOfLe hUC), hIdx⟩

end CFSG.LieType.Chevalley
