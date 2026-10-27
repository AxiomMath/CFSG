module

public import CFSG.GF2Type.SmithTypeE.DMod.TD6
public import CFSG.GF2Type.SmithTypeE.E7.Omega
public import CFSG.LargeExtraspecial.A2ModOrdCard

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod


theorem lieModel_TD6 : CFSG.Blueprint.LieModel ↥TD6 .POmegaPlus 6 2 1 :=
  lieModel_of_mulEquiv_timmesfeldOmegaPlus 6 (by norm_num) omegaTD6.symm

theorem card_TD6 : Nat.card ↥TD6 = CFSG.Open.ordD 6 2 :=
  (CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_POmegaPlus lieModel_TD6).2

end CFSG.GF2Type.SmithTypeE.DMod
