module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCycExc
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuter
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLieCharRankProof
public import CFSG.LieType.SeitzGeneration.Defs
public import CFSG.Sporadic.Bridge.Catalogue
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCycVacuous
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeOut

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.AGLEmbeddingD2

section Inputs

theorem kFactSeitzCyc_of_inputsLow (hRank : KFactLieCharRank) (hOut : KFactLieCharOut)
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (TauCeti.CFSGIndex.sporadic s).Group))
    (hS : CFSG.LieType.SeitzGeneration.KFactSeitzRankTwoLow) : KFactSeitzCyc := by
  intro K _ _ _ hnab ⟨i, ⟨e⟩⟩ p hp hp2 T _ hTc E hE hEcard hnotInn hfix
  have hone := pRank_le_one_of_isCyclic_sylow hp T hTc
  rcases i with ⟨q, hq⟩ | ⟨n, hn⟩ | ⟨⟨d, hv⟩⟩ | s
  · exact (false_of_cyclic_index hnab q hq e).elim
  · exact (false_of_alternating n hn e hp hp2 hE hnotInn).elim
  · by_cases hpc : p = d.characteristic
    · exact (false_of_lie_char hRank hOut ⟨d, hv⟩ e hp hp2 hpc T hTc hE hnotInn).elim
    by_cases hex : IsD2SeitzException p d
    swap
    · exfalso
      refine hfix (closure_fixed_eq_top_of_map_congr e E ?_)
      exact hS ⟨d, hv⟩ p hp hp2 hpc hex _ (isElemAbelian_map_congr e hE)
        (by rw [card_map_congr, hEcard])
        (CFSG.LieType.SeitzGeneration.RankLE2.of_mulEquiv e
          (CFSG.LieType.SeitzGeneration.RankLE2.of_pRank hp (hone.trans (by norm_num))))
    rcases hex with ⟨rfl, hcase⟩ | ⟨rfl, hcase⟩
    · rcases hcase with ⟨q, hq2, hqe, rfl⟩ | ⟨q, hq2, hqe, rfl⟩ | ⟨q, hq2, hqe, rfl⟩ |
        ⟨q, hq2, hqe, rfl | rfl⟩ | rfl
      · exact ⟨⟨.A 1 q, hv⟩, Or.inl ⟨rfl, q, hq2, hqe, rfl⟩, ⟨e⟩⟩
      · have := two_le_pRank_three_linThreeFour q hq2 hqe hv e
        omega
      · have := two_le_pRank_three_unitaryFour q hq2 hqe hv e
        omega
      · have := two_le_pRank_three_typeB 3 le_rfl q hq2 hqe hv e
        omega
      · have := two_le_pRank_three_typeB 4 (by norm_num) q hq2 hqe hv e
        omega
      · exact (hnotInn (le_range_conj_of_not_dvd_card_outer hp
          (not_dvd_card_outer_tits hv e hp hp2) hE)).elim
    · rcases hcase with rfl | rfl
      · exact (hnotInn (le_range_conj_of_not_dvd_card_outer hp
          (not_dvd_card_outer_tits hv e hp hp2) hE)).elim
      · exact ⟨⟨.suzuki 2, hv⟩, Or.inr ⟨rfl, rfl⟩, ⟨e⟩⟩
  · exact (false_of_sporadic hOutS s e hp hp2 hE hnotInn).elim

end Inputs

section Main

theorem kFactSeitzCyc_of_seitzLow (hS : CFSG.LieType.SeitzGeneration.KFactSeitzRankTwoLow) :
    KFactSeitzCyc :=
  kFactSeitzCyc_of_inputsLow kFactLieCharRank kFactLieCharOut
    (not_dvd_card_outer_sporadic CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group) hS

theorem kFactSeitzCyc_of_seitz (hS : KFactSeitzRankTwo) : KFactSeitzCyc :=
  kFactSeitzCyc_of_seitzLow hS.low

end Main

end CFSG.AGLEmbedding
