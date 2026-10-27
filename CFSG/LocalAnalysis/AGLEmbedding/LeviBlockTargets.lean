module

public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.AGLEmbedding.LeviBlock

open CFSG.Open

theorem card_catGroup_u38 {d : TauCeti.ValidLieTypeIndex} (hd : IsUThreeEightIndex d) :
    Nat.card (CatGroup d) = 5515776 := by
  obtain ⟨q, hqp, hqe, hdq⟩ := hd
  rw [card_catGroup_twistedA hdq, hqp, hqe]
  unfold ordTwistedA
  decide

theorem catGroup_u42_facts {d : TauCeti.ValidLieTypeIndex} (hd : IsUFourTwoIndex d) :
    Nat.card (CatGroup d) = 25920 ∧ IsSimpleGroup (CatGroup d) := by
  obtain ⟨q, hqp, hqe, hdq⟩ := hd
  refine ⟨by rw [card_catGroup_twistedA hdq, hqp, hqe]; unfold ordTwistedA; decide, ?_⟩
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.twistedA 3 q := hdq
  exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ _ _ _
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv (MulEquiv.refl _))).2

end CFSG.AGLEmbedding.LeviBlock
