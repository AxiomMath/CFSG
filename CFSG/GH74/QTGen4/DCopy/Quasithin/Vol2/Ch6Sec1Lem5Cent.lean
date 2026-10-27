module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5CentD
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5Cut
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5CentS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement

section Assembly

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

theorem res615Cent_of_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (hR : RankTwoThreeClassTwo) :
    Res615Cent_F4 := fun _ _ _ _ _ _ _ _ _ c =>
  c.le_pCoreOf_of_le_commutator_ch615_F4 h331 h432 (c.le_commutator_sup_ch615_F4 h331 hR)

end Assembly

end CFSG.Quasithin.H13
