module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusAut
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicProof
import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.ComponentClassification.OuterAutomorphisms

theorem false_of_cyclic_sylow (hOut : KFactOutCyclic) {p r : ℕ} {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup S)
    (P : Sylow p S) (hP : IsCyclic (P : Subgroup S)) {E : Subgroup (MulAut S)} {ζ γ : MulAut S}
    (h : SPLAutData p r S E ζ γ) : False := by
  have hp := h.prime_p
  have : Fact p.Prime := ⟨hp⟩
  have hout : CFSG.Open.pRank p (⊤ : Subgroup (Outer S)) ≤ 1 :=
    hOut S hs hnab hcat p hp h.ne_two P hP
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple hnab
  have hmul := CFSG.LocalAnalysis.RankFourTheoremC.pRank_mulAut_le_add_pRank_outer hp hZ
  have hS : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1 :=
    CFSG.SectionRank.pRank_le hp.one_lt fun A _ hA => by
      rw [pow_one]
      exact CFSG.AGLEmbedding.card_le_of_isElemAbelian_of_isCyclic_sylow P hP hA
  have h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut S)) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top h.elem h.card
  omega

end CFSG.HardMathSupport.Curtis.Coordinator
