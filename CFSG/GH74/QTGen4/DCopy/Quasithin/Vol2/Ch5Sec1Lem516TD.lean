module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem515

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

variable {T M L H X W : Subgroup G} {n : ℕ}

namespace Hyp5_0_1

variable (h : Hyp5_0_1 G T M L n)
include h

theorem caseI_D_F4 (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (hH : IsHStar T M H) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) :
    H ⊓ M ≤ Subgroup.normalizer (oTwoUpper (T ⊔ D) : Set G) := by
  rw [sup_comm]
  exact (h.lemma_5_1_5_one_F4 h331 hR hH hD).2

end Hyp5_0_1

end CFSG.Quasithin.H13
