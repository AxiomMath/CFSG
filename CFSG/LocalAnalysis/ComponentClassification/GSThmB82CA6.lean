module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Set3

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Eight2

variable {X : Type} [Group X] [Finite X]

namespace Setting3

variable (s : Setting3 X)

theorem Lay_le_centralizer : Seven.Lay s.h s.y ≤ centralizer (s.h.secB0 s.y : Set X) :=
  Seven.Lay_le_centralizer_secB0 s.h s.y

theorem G0_le_normalizer_Lay : s.h.secG0 s.y ≤ normalizer (Seven.Lay s.h s.y : Set X) :=
  Seven.secG0_le_normalizer_Lay s.h s.y

theorem map_Lay_eq : ((Seven.Lay s.h s.y).subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) =
    generalizedFitting (s.h.subQuot s.y) :=
  s.toSetting1.map_Lay_eq

theorem exists_setting3_Lay : ∃ s' : Setting3 X, s'.toSetting1 = s.toSetting1 ∧
    s'.t ∈ Seven.Lay s.h s.y ∧ s'.t * s'.t ∈ s.h.S ⊓ s.h.secG0 s.y :=
  s.toSetting2.exists_setting3

end Setting3

end Eight2

end CFSG.ComponentClassification.GSThmB
