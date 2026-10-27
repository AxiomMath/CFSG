module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResKacNodes

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Dickson.Sec6.I1431.ExcKacCheck
  CFSG.HardMathSupport.Dickson.Sec6.I1431.ExcKacNodes

theorem excKac_f4 :
    ExcKac Tag.F4 :=
  excKac_of_checks kacF4 facts_F4 f4E f4G f4bnd f4_hbnd f4_hadj f4_hdist f4_hG f4_Q1
    (fun _ => f4_Q2) (fun h => absurd h (by decide))

theorem excKac_e6 :
    ExcKac Tag.E6 :=
  excKac_of_checks kacE6 facts_E6 e6E e6G e6bnd e6_hbnd e6_hadj e6_hdist e6_hG e6_Q1
    (fun h => absurd h (by decide)) (fun _ => e6_Q3)

theorem excKac_e7 :
    ExcKac Tag.E7 :=
  excKac_of_checks kacE7 facts_E7 e7E e7G e7bnd e7_hbnd e7_hadj e7_hdist e7_hG e7_Q1
    (fun h => absurd h (by decide)) (fun _ => e7_Q3)

theorem excKac_e8 :
    ExcKac Tag.E8 :=
  excKac_of_checks kacE8 facts_E8 e8E e8G e8bnd e8_hbnd e8_hadj e8_hdist e8_hG e8_Q1
    (fun _ => e8_Q2) (fun h => absurd h (by decide))

end CFSG.HardMathSupport.Dickson.Sec6.I1431
