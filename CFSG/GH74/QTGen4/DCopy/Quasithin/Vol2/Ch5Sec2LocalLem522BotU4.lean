module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522BotList
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522BotW
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotU4

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

theorem stmt5_2_2_bot_U4_of_F4 (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) :
    Stmt5_2_2_bot_U4_F4 := by
  intro G _ _ T M L V H B D L₂ Dp n hyp _ _ _ _ hsp _ _ _ _
  obtain ⟨-, -, hWc, -, h16⟩ := hyp.commutator_facts_F4 h510 h331 hR
  exact false_of_sixteen_le_of_isSpecialPow hsp (hyp.commutator_le_pCoreOf_F4 h510 h331 hR) hWc h16

end CFSG.Quasithin.H13
