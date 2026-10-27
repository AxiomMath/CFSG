module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Basic

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615

variable (c : Cx615 G T M L V H n)
include c

theorem minParabolic_F4 (h331 : Stmt3_3_1_F4) : MinParabolic H T (H ⊓ M) :=
  (c.hyp.toHyp5_0_1.minParabolic_of_isHStar_F4 h331 c.hH).1

end Cx615

end CFSG.Quasithin.H13
