module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTOmUnit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTOmRestr
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTOmMinus6
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTOmPlus4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open OmegaCanon

theorem omegaUnitaryInOm8_holds : OmegaUnitaryInOm8 CFSG.AGLEmbedding.Om8 :=
  fun _ ht3 _ htΩ => spSupported_q2_le_om8 ht3 htΩ

theorem omegaOrthRank2Solvable_holds : OmegaOrthRank2Solvable CFSG.AGLEmbedding.Om8 := by
  intro t ht3 ht1 htΩ hm
  obtain ⟨e⟩ := nonempty_spSupported_inf_om8_equiv ht3 ht1
  have h4 : Module.finrank (ZMod 2) ↥(fixV t) = 4 := by
    have := finrank_fixV ht3 ht1
    omega
  haveI := isSolvable_omegaGroup_plus_four (fixQ t) (fixQ_nondegenerate ht3 ht1) h4
    (ncard_fixQ_of_mult_two ht3 ht1 htΩ hm)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem omegaOrthRank1U4_holds : OmegaOrthRank1U4 CFSG.AGLEmbedding.Om8 := by
  intro t ht3 ht1 htΩ hm K hK
  obtain ⟨e⟩ := nonempty_spSupported_inf_om8_equiv ht3 ht1
  have h6 : Module.finrank (ZMod 2) ↥(fixV t) = 6 := by
    have := finrank_fixV ht3 ht1
    omega
  exact catalogIs_u4two_of_isComponentOf_of_equiv (fixQ t) (fixQ_nondegenerate ht3 ht1) h6
    (ncard_fixQ_of_mult_one ht3 ht1 htΩ hm) e hK

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
