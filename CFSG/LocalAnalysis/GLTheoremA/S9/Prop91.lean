module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Prop92

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem prop91 {p : ℕ} (hc : S9Ctx G p) (hin : Prop92Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : IsSStarMax p B x L) :
    CFSG.Open.IsQuasisimple ↥L ∧ IsChevSimple 2 (↥L ⧸ Subgroup.center ↥L) := by
  have h92 : H92 p B x L := H92.of_sstarMax hc.stage5 hc.stage8 h
  have hq := prop92 hc hin h92
  refine ⟨hq, ?_⟩
  obtain ⟨e⟩ := nonempty_pSimple_equiv hc.ctx.prime h92.comp hq
  exact (isChevSimple_congr e).1 h92.chev2

end CFSG.LocalAnalysis.GLTheoremA.S9
