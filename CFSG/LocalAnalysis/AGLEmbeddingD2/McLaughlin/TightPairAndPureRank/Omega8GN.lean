module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Omega8Cited
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicEngine

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding

theorem isChevTwo_of_omegaEightPlus {Y : Type} [Group Y] (h : IsOmegaEightPlus Y) :
    IsChevTwo Y := by
  obtain ⟨d, ⟨q, hq, hd⟩, he⟩ := h
  have hp2 := PrimePower.p_eq_two_of_card_eq_two hq
  refine Or.inl ⟨d, isChevIndexTwo_of_classical ?_, he⟩
  rw [hd]
  simp [IsClassicalOrG2Index, hp2]

theorem exists_perfect_of_gn (hGN : GlaubermanNilesInput) (hCov : KFactParabolicCoverOmega8)
    {X : Type} [Group X] [Finite X] {T : Subgroup X} (hX : GNSetting X T)
    (hC : ¬ 3 ∣ Nat.card (gnC T))
    (hD : ∀ T' : Subgroup X, T' ≠ ⊥ → T' ≤ T → (T'.subgroupOf T).Characteristic →
      Open.pRank 3 (Subgroup.normalizer (T' : Set X)) ≤ 2)
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hΩ : IsOmegaEightPlus (↥L ⧸ Subgroup.center ↥L)) (hΩL : IsOmegaEightPlus ↥L)
    (hS : IsSylowTwoOf (gnImg T T ⊓ L) L) :
    ∃ Ti : Subgroup X, Ti ≠ ⊥ ∧ Ti ≤ T ∧ (Ti.subgroupOf T).Characteristic ∧
      ∃ J : Subgroup (X ⧸ gnC T), J ≤ gnA T Ti L ∧ ⁅J, J⁆ = J ∧ 3 ∣ Nat.card J := by
  obtain ⟨T₁, T₂, hpair, hpar, -⟩ := hGN X T hX (hX.ne_bot_of_isComponentOf hL)
  have hT₁ : T₁ ≤ T := hpair.le_center.trans (QuasithinUnique.Setup.omegaOneCenterOf_le T)
  have hbound : ∀ Ti : Subgroup X, Ti ≠ ⊥ → Ti ≤ T → (Ti.subgroupOf T).Characteristic →
      Open.pRank 3 (gnA T Ti L) ≤ 2 := fun Ti h1 h2 h3' =>
    ((CFSG.SectionRank.pRank_mono (by norm_num) inf_le_left).trans
      (pRank_gnImg_le T hC _)).trans (hD Ti h1 h2 h3')
  have hcov := hCov (X ⧸ gnC T) L (gnImg T T ⊓ L) (gnA T T₁ L) (gnA T T₂ L) hΩL hS ?_
    (hbound T₁ hpair.ne_bot₁ hT₁ hpair.char₁) (hbound T₂ hpair.ne_bot₂ hpair.le₂ hpair.char₂)
  · rcases hcov with h | h
    · exact ⟨T₁, hpair.ne_bot₁, hT₁, hpair.char₁, h⟩
    · exact ⟨T₂, hpair.ne_bot₂, hpair.le₂, hpair.char₂, h⟩
  · intro P hP
    rcases hpar L hL (isChevTwo_of_omegaEightPlus hΩ) P hP with h | h
    · left
      refine le_inf ?_ ((pElementSubgroup_le P).trans hP.1)
      exact h.trans (Subgroup.map_mono (Subgroup.centralizer_le_normalizer _))
    · right
      exact le_inf h ((pElementSubgroup_le P).trans hP.1)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
