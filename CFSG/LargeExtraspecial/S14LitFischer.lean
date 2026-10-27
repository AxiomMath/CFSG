module

public import CFSG.LargeExtraspecial.S12Fischer
public import CFSG.Milestones.CL_LIT_Fischer_three_transposition_theorem

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

theorem s12FischerStatement :
    S12FischerStatement :=
  fun G _ _ D hclass hinv hprod hgen hcenter hsimple =>
    CFSG.Milestones.cl_lit_fischer_three_transposition_theorem G D hclass hinv hprod hgen
      hcenter hsimple

end CFSG.LargeExtraspecial.S14
