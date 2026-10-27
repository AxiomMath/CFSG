module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5FH
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5FJ
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5FXS432
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5GDS432

public section
namespace CFSG.Quasithin.H13

open Equiv CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.QuasithinUnique.L246C127
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

theorem res615EFF_ch615_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (hB56 : AsB56) : Res615EFF_F4 :=
  res615EFF_of_cases134_F4 h331 h432 hB56 fun _ _ _ _ _ _ _ _ _ c hU hN h => by
    rcases h with h1 | h3 | h4
    · exact c.exists_of_b56Case1_ch615_F4 h432 hU hN h1
        (fun h7 hfix => c.exists_of_case1_alt_seven_ch615 hU hN h1 h7 hfix)
        (fun hh => (c.false_of_case1_hat_ch615_F4 h432 hU hN h1 hh).elim)
    · exact (c.false_of_b56Case3_ch615_F4 h331 h432 hU hN
        (fun F hF => factorFacts_of_b56FactorList_ch615 F hF) h3).elim
    · exact c.exists_of_b56Case4_ch615 hU hN h4

end CFSG.Quasithin.H13
