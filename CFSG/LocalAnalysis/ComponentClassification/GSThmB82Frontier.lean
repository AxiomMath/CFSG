module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Set3

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Eight2

variable {X : Type} [Group X] [Finite X]

abbrev Setting3.Dt (s : Setting3 X) : Subgroup X := conjugate s.h.D s.t

end Eight2

end CFSG.ComponentClassification.GSThmB
