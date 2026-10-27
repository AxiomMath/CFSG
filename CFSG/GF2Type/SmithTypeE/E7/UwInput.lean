module

public import CFSG.GF2Type.SmithTypeE.E7.DivBase
public import CFSG.GF2Type.SmithTypeE.E7.UwRoots

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7


theorem uwInput : UWInput :=
  ⟨orbit_roots, ncard_mid, fun hj hj' => exists_stab0_mid hj hj'⟩

end CFSG.GF2Type.SmithTypeE.E7
