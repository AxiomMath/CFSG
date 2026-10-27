module

public import CFSG.LargeExtraspecial.S3bConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Matrix
open scoped MatrixGroups

@[expose] def DW37WidthFourStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G),
    S.width = 4 → g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ≠ S.z → S.IsReducible →
    Nonempty (G ≃* PSL(S.width + 2, ZMod 2))

end CFSG.LargeExtraspecial.DW
