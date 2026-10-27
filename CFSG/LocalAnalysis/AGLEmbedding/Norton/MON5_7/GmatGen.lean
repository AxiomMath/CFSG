module

public import CFSG.Monster.SteinbergMY443NativeSurjective

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Monster.Generated CFSG.YGroups.Y443

theorem closure_range_gGen_eq_top :
    Subgroup.closure (Set.range gGen) = ⊤ := by
  rw [← f443_range]
  exact MonoidHom.range_eq_top.2
    ((y443_native_surjective_homomorphism.2 f443 f443_of))

end CFSG.AGLEmbedding.Norton.MON5_7
