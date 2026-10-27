module

public import CFSG.GF2Type.Aschbacher1977.WidthTwo
public import CFSG.GF2Type.Aschbacher1977WidthAtMostTwo
import CFSG.GF2Type.Aschbacher1977.WidthOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Aschbacher1977

open CFSG CFSG.Blueprint

theorem aschbacher1977WidthAtMostTwo_holds
    : Aschbacher1977WidthAtMostTwoStatement := by
  intro G _ _ _ hnonab z hz hext w hcard
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact lieModel_or_sporadic_of_width_one G hnonab hz hext hcard
  · rintro rfl
    exact width_two_classification G hnonab hz hext hcard

end CFSG.GF2Type.Aschbacher1977
