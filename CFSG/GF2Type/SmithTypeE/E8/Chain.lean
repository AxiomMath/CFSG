module

public import CFSG.GF2Type.SmithTypeE.E8.Assembly
public import CFSG.GF2Type.SmithTypeE.E8.Path
public import CFSG.GF2Type.SmithTypeE.E8.Levi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 CFSG.RankThree.PartTwo.Sec21
  CFSG.GF2Type.SmithTypeE.E8

theorem partD_of_chain (hAS : AschbacherSmithWideInput) (hDW : DW.DW37Statement)
    (hHolt : HoltUniqueFixedPointSimple) (hE7 : SmithE7Input) (h33 : SmithE8E33)
    (h34Q : SmithE8E34Q) (h23 : SmithE8E23) (h24 : SmithE8E24) (hLine : SmithE8E24Line)
    (h25 : SmithE8E25) (h23f : SmithE8E23Four) (h261 : SmithE8E261) : PartD := by
  obtain ⟨h34a, h34b⟩ := smithE8E34_of h33 h34Q
  exact partD_of_props hAS hDW hHolt hE7 (smithE8LocalInput_of h34a h34b h23 h24 h25 h23f)
    (smithE8PathInput_of h34a h34b h23 h24 h25 h23f hLine (smithE8E421Three_of h34a h261))

end CFSG.GF2Type.SmithTypeE
