module

public import CFSG.LocalAnalysis.SectionRank.AlternatingCover

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

theorem le_pRank_of_elemAbelian_card {p k : ℕ} (hp : 1 < p) {G : Type*} [Group G] [Finite G]
    {H E : Subgroup G} (hEH : E ≤ H) (hE : CFSG.Open.IsElemAbelian p E) (hc : Nat.card E = p ^ k) :
    k ≤ CFSG.Open.pRank p H := CFSG.SectionRank.le_pRank hp hEH hE hc

theorem two_le_pRank_three_alternating {n : ℕ} (hn : 6 ≤ n) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) :=
  le_pRank_of_elemAbelian_card (p := 3) (k := 2) (by norm_num) le_top
    (CFSG.SectionRank.isElemAbelian_sylowThreeAlt hn) (CFSG.SectionRank.card_sylowThreeAlt hn)

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

end
