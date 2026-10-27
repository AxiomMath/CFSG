module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BRes
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8TD4
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Lab
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Om

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265


theorem quBRes_holds : QUBRes := by
  intro Ω _ _ S B T x b hN hJ hB hTB
  by_cases hc : (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω)
  · exact (hN.false_of_comm_le_centralizer hJ hB hTB hc).elim
  have hF := hN.cfg.fieldOn_of_unTwo hJ
  obtain ⟨labK, hkind, hlab⟩ := S265BU8.exists_label_of_fieldOn_unTwo hN.cfg.comp hF
    (hN.cfg.elem.2 b hN.cfg.hb) hN.cfg.ipart hJ
  exact S265BU8.qUConcl_of_u8 hN.cfg hF hkind hlab hB.ge hc

end CFSG.LocalAnalysis.GLTheoremA.S265

end
