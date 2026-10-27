module

public import CFSG.LocalAnalysis.SectionRank.QTK.Interface
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenLinear
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth

public section

namespace CFSG.SectionRank.QTK

open CFSG.Assembly.LowTwoRank

theorem qtEvenClassicalRestriction_holds : QTEvenClassicalRestriction := by
  intro S _ _ t n f hQT hm
  cases t with
  | PSL => exact qtkSimpleList_of_psl_even hQT hm
  | PSU => exact qtkSimpleList_of_psu_even hQT hm
  | PSp => exact qtkSimpleList_of_psp_even hQT hm
  | POmegaOdd => exact (hm.1.2.2.2 rfl).elim
  | POmegaPlus => exact absurd hQT (not_evenRank_le_two_of_omegaPlus_even hm)
  | POmegaMinus => exact absurd hQT (not_evenRank_le_two_of_omegaMinus_even hm)
  | _ => exact hm.2.elim

end CFSG.SectionRank.QTK
