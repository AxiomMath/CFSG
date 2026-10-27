module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5S
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem518DLOS331

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Setting

variable {G : Type} [Group G]

namespace Setting518D5

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D D₃ D₅ : Subgroup G} {n : ℕ}
  (s : Setting518D5 G T M L V H B D D₃ D₅ n)
include s

theorem B_le_normalizer_z518_F4 (hF : L2TorusFact) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) :
    B ≤ Subgroup.normalizer (z518 T L D₅ : Set G) := by
  have hBL : B ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    (le_sup_right.trans le_sup_left).trans
      (s.hyp.DBT_le_normalizer_inf_L_of_le_F4 h331 hR (d518_le H D))
  have hBD : B ≤ Subgroup.normalizer (D₅ : Set G) := fun b hb =>
    mem_normalizer_of_le_isCyclic (s.isCyclic_D hF) s.D₅_le (s.hyp.notation59.2.2 hb)
  exact le_normalizer_sup_of_le hBL hBD

end Setting518D5

end Setting

end CFSG.Quasithin.H13
