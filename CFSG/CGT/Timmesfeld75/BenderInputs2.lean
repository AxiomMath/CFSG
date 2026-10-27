module

public import CFSG.CGT.Timmesfeld75.Reduction
import CFSG.CGT.Timmesfeld75.BenderInputsBasic

public section

namespace CFSG.CGT.Timmesfeld75

theorem benderSimpleInput_of_repo : BenderSimpleInput := by
  intro K _ hK
  have := finite_of_isBenderGroup hK
  exact CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hK

end CFSG.CGT.Timmesfeld75
