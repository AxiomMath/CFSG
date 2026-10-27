module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.Helpers

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ComponentClassification

theorem kProper_subgroup {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X) {G : Type} [Group G]
    (hK : CFSG.Assembly.KProper C G) (H : Subgroup G) : CFSG.Assembly.KProper C H :=
  CFSG.KCore.KProperNonab.subgroup hC hK H

end CFSG.LocalAnalysis.ComponentInitial
