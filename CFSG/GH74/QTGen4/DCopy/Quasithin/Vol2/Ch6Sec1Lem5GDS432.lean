module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5GB
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5GD

public section
namespace CFSG.Quasithin.H13

open Equiv CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.QuasithinUnique.L246C127
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_case1_hat_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (h1 : B56Case1 (ffJ (autI hU (borelL T L ⊔ H))))
    (hh : IsHat ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))))
      ↥(alternatingGroup (Fin 6))) : False := by
  by_cases hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = ⊥
  · exact c.false_of_case1_hat_nofix_ch615 hU hN h1 hh hfix
  · exact c.false_of_case1_hat_fix_ch615_F4 h432 hU hN hh hfix

end Cx615C

end CFSG.Quasithin.H13
