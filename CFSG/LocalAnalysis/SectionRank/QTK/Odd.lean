module

public import CFSG.LocalAnalysis.SectionRank.QTK.Interface
public import CFSG.LocalAnalysis.SectionRank.QTK.OddLinear
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth

public section

namespace CFSG.SectionRank.QTK

open CFSG.Assembly.LowTwoRank

theorem qtOddClassicalRestriction_holds : QTOddClassicalRestriction := by
  intro S _ _ t n p f hp2 hQT hm
  cases t with
  | PSL => exact qtkSimpleList_of_psl_odd hp2 hQT hm
  | PSU => exact qtkSimpleList_of_psu_odd hp2 hQT hm
  | PSp => exact qtkSimpleList_of_psp_odd hp2 hQT hm
  | POmegaOdd => exact absurd hQT (not_evenRank_le_two_of_omegaOdd hm)
  | POmegaPlus => exact absurd hQT (not_evenRank_le_two_of_omegaPlus hp2 hm)
  | POmegaMinus => exact absurd hQT (not_evenRank_le_two_of_omegaMinus hp2 hm)
  | _ => exact hm.2.elim

end CFSG.SectionRank.QTK
