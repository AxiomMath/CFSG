module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL4S331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3T325A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3T325L
public import CFSG.Quasithin.Vol2.Ch3T325T

public section
namespace CFSG.Quasithin.H13

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem stmt3_2_5_of_c0_F4 (h316 : Theorem316Statement) (hD310 : D310C0) (h331 : Stmt3_3_1_F4)
    (h3222 : Vol2.Ch10.TmpL6_3_2_2_two) (h3228 : Vol2.Ch10.TmpL6_3_2_2_eight)
    (h4 : Vol2.Ch11.TmpL6_3_2_2_four) (h6 : Vol2.Ch11.TmpL6_3_2_2_six_F4) (h56 : AsB56) :
    Stmt3_2_5_F4 := by
  intro G _ _ T L V₀ hfsu hL
  have c := T325.Ctx.of_F4 h331 h3222 h3228 hfsu hL
  have : IsMulCommutative ↥(conjClosure V₀ T) := c.elemV.1
  have : IsMulCommutative
      ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))) := c.elemVM.1
  refine ⟨T325.qhat_V h316 c, T325.qhat_VM h316 c, ?_⟩
  by_cases hC : V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥
  · by_cases hV : V₀ = conjClosure V₀ T
    · exact Or.inr (Or.inl (c.case_two hC hV))
    · exact Or.inr (Or.inr (c.case_three_c0 h316 hD310 h4 hC hV))
  · exact Or.inl (c.case_one_F4 h56 h6 hC)

end CFSG.Quasithin.H13
