module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCJ2Aut

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open CFSG.ComponentClassification

theorem outerData_P :
    OuterData ↥CFSG.ComponentClassification.J2Cover.Models.P :=
  OuterData.of_mulEquiv (MulEquiv.subgroupCongr J2Cover.Models.P_eq_autP.symm) outerData_autP

end CFSG.EvenSporadicStandard.Fin76b.J2
