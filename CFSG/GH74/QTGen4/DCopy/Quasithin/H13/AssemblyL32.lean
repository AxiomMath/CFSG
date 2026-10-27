module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsFSU

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

theorem stmt14_8_1_three_of_inputs_F4 (h1332 : Stmt13_3_2_three_fsu_F4) (hU43 : StmtU43NoL32Local)
    (h14414 : Stmt14_4_14_F4) (h14775 : Stmt14_7_75_F4) : Stmt14_8_1_three_F4 := by
  intro G _ _ T L hH hL32
  by_cases hSp : LieModel G .PSp 3 2 1
  · exact Or.inl hSp
  by_cases hU : LieModel G .PSU 4 3 1
  · exact absurd hL32 (hU43 G T L hU hH.sylow hH.faithful.1)
  have hyp : Hyp14_3_1One G T L := ⟨hH, hL32, hSp, hU⟩
  obtain ⟨⟨V, hV⟩, hall⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, -, hF⟩ := hall V hV
  by_cases hab : IsMulCommutative ↥(fsuU T V)
  · exact Or.inr (Or.inr (Or.inr (h14775 G T L V hyp hF hab)))
  · rcases h14414 G T L V hyp hF hab with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)

end CFSG.Quasithin.H13
