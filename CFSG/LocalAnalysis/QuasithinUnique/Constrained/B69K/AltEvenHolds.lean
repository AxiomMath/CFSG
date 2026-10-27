module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltEven

public section

namespace CFSG.Quasithin

namespace B69K

theorem asAltEven_holds : AsAltEven := by
  intro Y _ _ K T M hAS m hm hev
  rintro ⟨e⟩
  exact false_of_alt_pair hAS (Or.inr (by omega)) e fun T' hT' => alt_pair_even hm hev T' hT'

end B69K

end CFSG.Quasithin
