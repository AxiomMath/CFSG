module

public import CFSG.GF2Type.SmithTypeE.E8.FactsWord

public section

namespace CFSG.GF2Type.SmithTypeE.E8


theorem e23FourFacts8 : E23FourFacts8 where
  tv_invol r hr := F.isRootInvol_mul_self hr
  word r hr w hw w' hw' hc hc' := F.word_core hr hw hw' hc hc'
  plane r r' hr hr' hncomm hnbraid := F.plane_core hr hr' hncomm hnbraid

theorem smithE8E23Four_of_model (hM : SmithE8Model) (h33 : SmithE8E33) (h34a : SmithE8E34a)
    (h34b : SmithE8E34b) (h24 : SmithE8E24) : SmithE8E23Four :=
  smithE8E23Four_of e23FourFacts8 hM h33 h34a h34b h24

end CFSG.GF2Type.SmithTypeE.E8
