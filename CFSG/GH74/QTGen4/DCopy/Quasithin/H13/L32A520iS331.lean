module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32A520i

public section
namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Holt
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

omit [CFSG.GH74.QTGen4.Finite4 G] in
theorem c1_le_H_F4 (T L V H Y : Subgroup G) : c1 T L V H Y ≤ H :=
  inf_le_left.trans (centralizerSection_le_left _ _ _)

end CFSG.Quasithin.H13.L32A
