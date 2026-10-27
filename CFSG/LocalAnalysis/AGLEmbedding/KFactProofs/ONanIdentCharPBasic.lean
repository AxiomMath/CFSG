module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem isCyclic_sylow_of_pRank_le_one {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : Open.pRank p (⊤ : Subgroup K) ≤ 1) (T : Sylow p K) :
    IsCyclic (T : Subgroup K) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p (T : Subgroup K)) := ⟨T.isPGroup'⟩
  by_contra hnc
  obtain ⟨E, -, hcard, hel⟩ := CFSG.lemma_4_5_a hp2 hnc
  have hE : IsElemAbelian p (E.map (T : Subgroup K).subtype) :=
    CFSG.SectionRank.isElemAbelian_map
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).mp hel) _
  have hEcard : Nat.card (E.map (T : Subgroup K).subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcard]
  have := CFSG.SectionRank.le_pRank hp.one_lt le_top hE hEcard
  omega

end CFSG.AGLEmbedding
