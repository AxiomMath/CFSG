module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3L3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3L3Semi

public section

namespace CFSG.Quasithin.H13

theorem stmt5_3_L3_facts_of_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4) : Stmt5_3_L3_facts_F4 := by
  intro G _ _ T M L V H B D L₂ n f hyp hty hf
  exact ⟨Sec53L3.l3facts_one_F4 h527 h531 hyp hty hf, Sec53L3.l3facts_two_F4 h527 hyp hty hf,
    Sec53L3.l3facts_three_F4 h527 hyp hty hf, Sec53L3.l3facts_four_F4 h527 hyp hty hf,
    Sec53L3.l3facts_five_F4 h527 h531 hyp hty hf,
    fun hf3 => Sec53L3.l3facts_six_of_three_le_F4 h527 h531 hyp hty hf hf3⟩

end CFSG.Quasithin.H13
