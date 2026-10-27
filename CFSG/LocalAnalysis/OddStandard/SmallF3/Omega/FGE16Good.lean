module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78Inputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem fg_asc82E16Good_of_center
    (hZ : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L → centerIn L = ⊥) :
    Asc82E16Good := by
  intro G _ _ K hK B hB hBK h5
  exact fg_exists_sylow_normalE16 hK (hZ G K hK) hB hBK h5

theorem asc82E16Good_of (hP : Asc82Tab6P) : Asc82E16Good :=
  fg_asc82E16Good_of_center hP.center_triv

end CFSG.OddStandard.SmallF3.Omega
