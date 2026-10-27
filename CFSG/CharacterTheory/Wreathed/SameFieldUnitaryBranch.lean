module

public import CFSG.CharacterTheory.Wreathed.SameFieldUnitaryCharacterTrivial
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueCore

public section

namespace CFSG.Wreathed.SameFieldUnitary

theorem dValueCore : DValueCoreStatement :=
  fun _ _ _ D hext htriv hpair hgw => D.d_value hext htriv hpair hgw

theorem unitaryBranch
    : CFSG.Wreathed.RecognitionFromGaps.UnitaryBranchStatement :=
  unitaryBranch_of_dValueCore dValueCore

end CFSG.Wreathed.SameFieldUnitary
