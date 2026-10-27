module

public import CFSG.GF2Type.SmithTypeE.E7.ModWt
public import CFSG.GF2Type.SmithTypeE.E7.ModBase
public import CFSG.GF2Type.SmithTypeE.E7.ModSteps

public section

namespace CFSG.GF2Type.SmithTypeE.E7


theorem e7ModelFacts : E7ModelFacts :=
  ⟨wt_ne_zero7, exists_adj7, wt_ne_xor7, tv_wt7, pair_rel_sym7, int_rel_sym7⟩

theorem smithE7E34Q_of_module (hM : SmithE7Module) : SmithE7E34Q :=
  smithE7E34Q_of e7ModelFacts hM

theorem smithE7E24Line_of_module (hM : SmithE7Module) : SmithE7E24Line :=
  smithE7E24Line_of e7ModelFacts hM

theorem smithE7E24_of_module (hM : SmithE7Module) : SmithE7E24 :=
  smithE7E24_of e7ModelFacts hM

theorem smithE7E23_of_module (hM : SmithE7Module) : SmithE7E23 :=
  smithE7E23_of e7ModelFacts hM

theorem smithE7E25_of_module (hM : SmithE7Module) : SmithE7E25 :=
  smithE7E25_of e7ModelFacts hM

end CFSG.GF2Type.SmithTypeE.E7
