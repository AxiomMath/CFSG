module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2SporNarrow3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.FusionCase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

theorem d2VacuousAt_of_datum {i : TauCeti.CFSGIndex} {p : ℕ}
    (h : ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* i.Group) → D2IndexDatum L p) :
    D2VacuousAt i p := by
  intro X _ _ R A X₀ K hK he
  have : Fact p.Prime := ⟨hK.prime⟩
  obtain ⟨hout, hd⟩ := h K he
  rcases hd with h2 | h3 | ⟨h3, hgen⟩ | hcore
  · exact h2 (hK.sq_dvd_card hout)
  · exact hK.false_of_three_le_pRank h3
  · exact hK.false_of_fusion_of_card hout h3 hgen
  · exact hK.false_of_core hout hcore

end CFSG.LocalAnalysis.RankThreeTheoremC
