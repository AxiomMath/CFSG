module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Plus
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Radical
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Quotient
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Extraspecial

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog.SideF4

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore

section Main


theorem isExtraspecial_QJ : CFSG.IsExtraspecial 2 ↥QJ :=
  isExtraspecial_two_of_central_involution t4G_mem_QJ t4G_sq t4G_ne_one
    (fun y _ => t4G_central y) (fun _ hx _ hy => commutator_mem_zpowers hx hy)
    (fun _ hx => sq_mem_zpowers hx) (centre_QJ_le exists_noncomm_QJ) exists_noncomm_QJ

theorem isPlusExtraspecial_QJ : IsPlusExtraspecial 4 QJ := by
  refine ⟨isExtraspecial_QJ, by rw [card_QJ]; norm_num, ?_⟩
  obtain ⟨E, hEQ, hE, hcard⟩ := exists_E_le_QJ
  exact ⟨E, hEQ, hE, by rw [hcard]; norm_num⟩

theorem isExtraspecialPlusByA5WrTwo_CJ : IsExtraspecialPlusByA5WrTwo CJ :=
  ⟨QJ, QJ_normal, isPlusExtraspecial_QJ, centralizer_QJ_le, nonempty_quotient_QJ⟩

end Main

end CFSG.EvenSporadicStandard.HNRecog.SideF4
