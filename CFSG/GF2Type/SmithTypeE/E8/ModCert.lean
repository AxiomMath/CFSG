module

public import CFSG.GF2Type.SmithTypeE.E8.FactsForm
public import CFSG.GF2Type.SmithTypeE.E8.FactsRel
public import CFSG.GF2Type.SmithTypeE.E8.ModSteps

public section

namespace CFSG.GF2Type.SmithTypeE.E8


theorem e8ModelFacts : E8ModelFacts where
  wt_ne_zero w hw := F.wt_ne_zero_core hw
  exists_adj w hw := F.exists_adj_core hw
  wt_ne_add w hw w' hw' h := F.wt_ne_add_core hw hw' h
  tv_wt r hr w hw := F.tv_wt_core hr hw
  pair_rel_sym r r' hr hr' hne := F.pair_rel_sym_core hr hr' hne
  int_rel_sym r r' hr hr' hne c c' h := F.int_rel_sym_core hr hr' hne c c' h

theorem smithE8E34Q_of_module (hM : SmithE8Module) : SmithE8E34Q :=
  smithE8E34Q_of e8ModelFacts hM

theorem smithE8E24Line_of_module (hM : SmithE8Module) : SmithE8E24Line :=
  smithE8E24Line_of e8ModelFacts hM

theorem smithE8E24_of_module (hM : SmithE8Module) : SmithE8E24 :=
  smithE8E24_of e8ModelFacts hM

theorem smithE8E23_of_module (hM : SmithE8Module) : SmithE8E23 :=
  smithE8E23_of e8ModelFacts hM

theorem smithE8E25_of_module (hM : SmithE8Module) : SmithE8E25 :=
  smithE8E25_of e8ModelFacts hM

end CFSG.GF2Type.SmithTypeE.E8
