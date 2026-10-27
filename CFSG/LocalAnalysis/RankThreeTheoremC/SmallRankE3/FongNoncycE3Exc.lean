module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankExc

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncyc

open CFSG.Open TauCeti CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank

set_option linter.unusedSectionVars false

section Exceptional

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge
  CFSG.TauCetiBridge.Even


theorem four_le_pRank_three_of_exceptional {S : Type} [Group S] [Finite S]
    (q : PrimePower) (d : ValidLieTypeIndex)
    (hd : (d.1 = .F4 q) ∨ (d.1 = .E6 q) ∨ (d.1 = .E7 q) ∨ (d.1 = .E8 q))
    (e : S ≃* ValidLieTypeIndex.Group d) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨i, hv⟩ := d
  rcases hd with rfl | rfl | rfl | rfl
  · obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.f4 q hv e
    have := four_le_pRank_three_adjointQuotient_any (τ := .F4) (Or.inl rfl) (K := K)
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
    exact this
  · obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.e6 q hv e
    have := four_le_pRank_three_adjointQuotient_any (τ := .E6) (Or.inr (Or.inl rfl)) (K := K)
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
    exact this
  · obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.e7 q hv e
    have := four_le_pRank_three_adjointQuotient_any (τ := .E7) (Or.inr (Or.inr (Or.inl rfl)))
      (K := K)
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
    exact this
  · obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.e8 q hv e
    have := four_le_pRank_three_adjointQuotient_any (τ := .E8) (Or.inr (Or.inr (Or.inr rfl)))
      (K := K)
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
    exact this

end Exceptional

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncyc

end
