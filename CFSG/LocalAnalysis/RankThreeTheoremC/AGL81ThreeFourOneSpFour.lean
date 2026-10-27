module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneTrivialOn
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFour
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesSpFour

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.AGLEmbedding.KlingenSpFour CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem signalizerThreeSpFour_holds : SignalizerThreeSpFour := by
  intro p hp hp5 q d hqp hq1 hd K _ _ ⟨eK⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ψ⟩ := nonempty_mulEquiv_psp4 hp2
    (statedClassicalModel_of_spFourIndex d ⟨q, Or.inl ⟨hqp, hq1, hd⟩⟩ eK)
  refine signalizerThreeOn_of_signalizerTrivialOn hp (by omega)
    (signalizerTrivialOn_of_model hp (IsPGroup.of_card (xS p).card_U) (fun V hV hnorm => ?_) ψ)
  refine Hyp111.mulAut_eq_bot_of_conj_xS hp2 V hV fun u hu => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => hnorm u hu v hv, fun hv => ?_⟩
  have := hnorm u⁻¹ (inv_mem hu) _ hv
  simpa [map_inv, mul_assoc] using this

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
