module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3Cover
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3Field

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.Open Subgroup TauCeti Chev3

section Certified


theorem t29Chev3_holds : T29Chev3 := by
  intro X _ _ L x h hm
  obtain ⟨m, hm3, ⟨e⟩⟩ := hm
  haveI : L.Normal := h.normal
  by_cases hZ : center ↥L = ⊥
  · have hle3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤ 3 := h.pRank_component_le
    rcases rank_dichotomy m hm3 ((mulEquivQuotientCenter hZ).trans e) with
      h4 | ⟨q, hq, hq27, h3⟩ | ⟨q, hq, hq3⟩ | ⟨q, hq, hq3⟩
    · exact absurd h4 (by omega)
    · obtain ⟨dd, hv⟩ := m
      change dd = .A 1 q at hq
      subst hq
      have hp : q.p = 3 := by simpa using hm3
      exact Or.inr (inducesFieldAutL227_of_setup h hZ hv hp hq27 h3 e)
    · exfalso
      obtain ⟨dd, hv⟩ := m
      change dd = .A 2 q at hq
      subst hq
      exact false_of_A_two_setup h hZ hv hq3 e
    · exfalso
      obtain ⟨dd, hv⟩ := m
      change dd = .twistedA 2 q at hq
      subst hq
      exact false_of_twistedA_two_setup h hZ hv hq3 e
  · exfalso
    exact false_of_cover_setup h hZ m hm3 e

end Certified

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
