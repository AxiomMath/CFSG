module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneLarge

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

theorem lemma55 (hF : Solomon75Frac53) (hN : Solomon75NoSwap) (h54 : Solomon75Lemma54p) :
    Solomon75Lemma55 := by
  intro X _ _ n z Z S h A A' hA hA'
  by_contra hne
  obtain ⟨s, hs⟩ := h.exists_sec5_inv
  have hS : Sec5S X n z Z S s := Sec5S.mk_of_hyps hF hN h54 h ⟨A, A', hA, hA', hne⟩ hs
  by_cases hn11 : n ≤ 11
  · exact hS.small_false hn11 hA hA' hne
  · exact hS.large_false hF hN (by omega) hA hA' hne

end CFSG.OddStandard.Solomon75
