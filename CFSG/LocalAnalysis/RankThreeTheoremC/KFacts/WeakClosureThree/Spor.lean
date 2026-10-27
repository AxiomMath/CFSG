module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.SporJ3
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.SporM
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicBMData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

theorem dichThreeAt_of_elemAbelian_mulEquiv {K L : Type} [Group K] [Finite K] [Group L]
    (e : K ≃* L) (h : ∃ E : Subgroup L, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4) :
    DichThreeAt K := by
  obtain ⟨E, hE, hc⟩ := h
  exact dichThreeAt_of_elemAbelian (E := E.map e.symm.toMonoidHom)
    ((isElemAbelian_map_iff_of_injective _ e.symm.injective E).2 hE)
    (by rw [Subgroup.card_map_of_injective e.symm.injective, hc])

section Spor


theorem dichThreeSpor_holds
    : DichThreeSpor := by
  intro K _ _ hs hnab ⟨s, ⟨e⟩⟩ h3
  haveI : Finite (NativeSporadic.Carrier s) := Finite.of_equiv K e.toEquiv
  have hcard : Nat.card K = Nat.card (NativeSporadic.Carrier s) := Nat.card_congr e.toEquiv
  by_cases hone : SporadicOnePair s 3
  · rcases hone with ⟨-, hs'⟩ | ⟨h5, -⟩ | ⟨h7, -⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
      rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
      · exact dichThreeAt_of_J3 e
      · exact dichThreeAt_of_elemAbelian_mulEquiv e CFSG.SectionRank.McL_elementary_three_rank_four
      · exact dichThreeAt_of_elemAbelian_mulEquiv e CFSG.SectionRank.Suz_elementary_three_rank_four
      · exact dichThreeAt_of_elemAbelian_mulEquiv e CFSG.SectionRank.ON_elementary_three_rank_four
      · exact dichThreeAt_of_elemAbelian_mulEquiv e CFSG.SectionRank.Co3_elementary_three_rank_four
      · exact dichThreeAt_of_elemAbelian_mulEquiv e CFSG.SectionRank.Co2_elementary_three_rank_four
      · exact dichThreeAt_of_elemAbelian_mulEquiv e CFSG.SectionRank.Co1_elementary_three_rank_four
      · exact dichThreeAt_of_elemAbelian_mulEquiv e
          CFSG.SectionRank.Fi22_elementary_three_rank_four
      · exact dichThreeAt_of_elemAbelian_mulEquiv e
          CFSG.SectionRank.Fi23_elementary_three_rank_four
      · exact dichThreeAt_of_elemAbelian_mulEquiv e
          CFSG.SectionRank.Fi24prime_elementary_three_rank_four
      · exact dichThreeAt_of_elemAbelian_mulEquiv e CFSG.SectionRank.HN_elementary_three_rank_four
      · exact dichThreeAt_of_elemAbelian_mulEquiv e CFSG.SectionRank.Ly_elementary_three_rank_four
      · exact dichThreeAt_of_elemAbelian_mulEquiv e CFSG.SectionRank.Th_elementary_three_rank_four
      · exact dichThreeAt_of_elemAbelian_mulEquiv e CFSG.SectionRank.B_elementary_three_rank_four
      · exact dichThreeAt_of_M e
    · omega
    · omega
  · rcases offPair_carrier CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicBMData_holds s 3
      Nat.prime_three (by norm_num) hone with h | ⟨h4, hp⟩
    · exact dichThreeAt_of_not_dvd_27 (by rw [hcard]; simpa using h)
    · exact dichThreeAt_of_pair (by rw [hcard]; simpa using h4)
        (hp.map e.symm.toMonoidHom e.symm.injective)

end Spor

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
