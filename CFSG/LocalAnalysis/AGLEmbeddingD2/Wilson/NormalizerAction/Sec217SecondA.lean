module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217U0
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217Frame
public import CFSG.RankThree.PartTwo.Sec21.Item215

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

@[expose] def Sec217SecondA : Prop :=
  ∀ (A E U : Subgroup G) (c : G) (L : Subgroup G), Cover217 A E U c L →
    ∃ a : G, Frame217 E c L a ∧ ∃ U₀ ∈ fourGroupsMinus E, U₀ ≤ iCore L a ∧
      ∃ K ∈ lThreeStarAt A a, (a, K) ∈ lThreeStarPairs A E U₀

section Main


set_option linter.unusedSectionVars false

theorem sec217SecondA_of (h45 : Sec4.Item4_5) (h215 : Item215) : Sec217SecondA (G := G) := by
  intro A E U c L h
  have hθ := sec217ThetaOne_holds A E U c L h
  have hAL := sec217ALe_of h45 A E U c L h
  obtain ⟨a₀, hfr₀⟩ := sec217Frame_of h45 A E U c L h
  obtain ⟨U₀, hU₀, hU₀I, hCE⟩ := h.exists_U0 hθ hAL hfr₀
  obtain ⟨b, hb, hbc, K, hK, hpair⟩ := h215 G A E U c L h.pair U₀ hU₀
  obtain ⟨hfrb, hI⟩ := h.frame_of_mem_D hθ hAL hfr₀ hb.1 (hCE b hb) hbc
  exact ⟨b, hfrb, U₀, hU₀, hI ▸ hU₀I, K, hK, hpair⟩

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
