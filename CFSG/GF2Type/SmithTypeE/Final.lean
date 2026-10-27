module

public import CFSG.GF2Type.SmithTypeE.GH74PartB
public import CFSG.GF2Type.SmithTypeE.E8.PartD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

theorem smith1980TypeE_of_gh74 (hgh : CFSG.LargeExtraspecial.AS35W.GH74Models) :
    GF2Type.Smith1980TypeEStatement :=
  smith1980TypeEStatement_of_parts (partA_partB_of_gh74 hgh).1 (partA_partB_of_gh74 hgh).2
    (partC_of_gh74_only hgh) (partD_of_gh74 hgh)

end CFSG.GF2Type.SmithTypeE
