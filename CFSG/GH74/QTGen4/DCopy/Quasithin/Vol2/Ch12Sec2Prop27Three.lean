module

public import CFSG.Quasithin.Vol2.Ch12Sec2Prop27Three
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Prop27

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem stmt12_2_27_of_F4 (hAsc : Asc94_M24He_L52Type_F4) (hM12 : CFSG.GH74.M12.S_Asc03_Theorem1)
    (h1226 : Stmt12_2_6_F4) : Stmt12_2_27_F4 := by
  intro G _ _ T L V hH hE n hn hB hV hML hVO hX
  refine ⟨fun h4 => ?_, fun h3 => ?_⟩
  · subst h4
    exact stmt12_2_27_four_F4 hAsc h1226 hH hE hB hV hML hVO hX
  · subst h3
    exact stmt12_2_27_three hM12 hH hE hB hV hML hVO hX

end CFSG.Quasithin.H13
