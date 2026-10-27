module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowEntries
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowRankThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowLinThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.Open

theorem kFactTenFourteenNarrowGamma_of
    (hM12 : ∀ (K : Type) [Group K] [Finite K],
      Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .M12).Group) →
      ∀ T : Sylow 3 K, narrowGamma 3 (T : Subgroup K) = ⊤)
    (hTits : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits → ∀ (K : Type) [Group K] [Finite K],
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ T : Sylow 3 K, narrowGamma 3 (T : Subgroup K) = ⊤)
    (hHS : ∀ (K : Type) [Group K] [Finite K],
      Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .HS).Group) →
      ∀ T : Sylow 5 K, narrowGamma 5 (T : Subgroup K) = ⊤)
    (hRu : ∀ (K : Type) [Group K] [Finite K],
      Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .Ru).Group) →
      ∀ T : Sylow 5 K, narrowGamma 5 (T : Subgroup K) = ⊤)
    (hHe : ∀ (K : Type) [Group K] [Finite K],
      Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .He).Group) →
      ∀ T : Sylow 7 K, narrowGamma 7 (T : Subgroup K) = ⊤) :
    KFactTenFourteenNarrowGamma := by
  intro p K _ _ T hp hp2 ⟨i, hi, ⟨e⟩⟩ hZ hrank hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hR3 : 3 ≤ Open.pRank p (⊤ : Subgroup K) → TenFourteenOneGroup p K := fun h3 =>
    absurd hrank (by have := le_pRank_sylow h3 T; omega)
  have hG : narrowGamma p (T : Subgroup K) = ⊤ → TenFourteenOneGroup p K := fun h => absurd h hne
  have hL : IsTenFourteenOneIndex p i → TenFourteenOneGroup p K := fun h => ⟨i, h, ⟨e⟩⟩
  cases i with
  | cyclic q hq => exact hi.elim
  | alternating n hn =>
    rcases hi with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
    · exact hL (Or.inl ⟨rfl, rfl⟩)
    · exact hR3 (three_le_pRank_a9 e)
    · exact hL (Or.inr ⟨rfl, rfl⟩)
  | lie d =>
    rcases hi with ⟨q, hqp, hqe, hd⟩ | ⟨q, hqp, hd⟩ | hsp | hl3 | ⟨hp3, m, hd⟩ |
      ⟨rfl, ⟨q, hq2, hq3, hd | hd | hd⟩ | ⟨q, hq2, hq2', hd⟩ | ⟨q, hq2, hq1, hd⟩ | hd⟩ |
      ⟨rfl, hd | hd | hd⟩
    · exact hL (Or.inl ⟨q, hqp, hqe, hd⟩)
    · exact hL (Or.inr (Or.inl ⟨q, hqp, hd⟩))
    · exact hR3 (three_le_pRank_spFour hp2 hsp e)
    · exact hG (narrowGamma_eq_top_linThree hp hp2 hl3 ⟨e⟩ T)
    · exact hL (Or.inr (Or.inr (Or.inl ⟨hp3, Or.inl ⟨m, hd⟩⟩)))
    · exact hL (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl ⟨q, hq2, hq3, hd⟩)⟩)))
    · exact hG (narrowGamma_eq_top_g28 ⟨q, hq2, hq3, hd⟩ e hZ T)
    · exact hG (narrowGamma_eq_top_sp48 ⟨q, hq2, hq3, hd⟩ e hZ T)
    · exact hL (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨q, hq2, hq2', hd⟩)⟩)))
    · exact hR3 (three_le_pRank_sp62 ⟨q, hq2, hq1, hd⟩ e)
    · exact hG (hTits d hd K ⟨e⟩ T)
    · exact hL (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl hd⟩)))
    · exact hL (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr hd⟩)))
    · exact hG (narrowGamma_eq_top_reeF4 hd e hZ T)
  | sporadic s =>
    rcases hi with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl⟩
    · exact hL (Or.inl ⟨rfl, rfl⟩)
    · exact hG (hM12 K ⟨e⟩ T)
    · exact hR3 (three_le_pRank_j3 e)
    · exact hL (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact hG (hHS K ⟨e⟩ T)
    · exact hG (hRu K ⟨e⟩ T)
    · exact hG (narrowGamma_eq_top_onan ⟨e⟩ T)
    · exact hG (narrowGamma_eq_top_fi24 ⟨e⟩ T)
    · exact hG (hHe K ⟨e⟩ T)
    · exact hL (Or.inr (Or.inr ⟨rfl, rfl⟩))

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
