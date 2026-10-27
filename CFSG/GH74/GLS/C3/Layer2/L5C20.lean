module

public import CFSG.GH74.GLS.C3.Layer2.L5C19
public import CFSG.GH74.GLS.C3.Layer2.L5C9b
public import CFSG.GH74.GLS.C3.Layer2.L5C4
public import CFSG.GH74.GLS.C3.Layer2.L5C5z
public import CFSG.GH74.GLS.C3.Layer2.L5C2f
public import CFSG.GH74.GLS.C3.Layer2.L5C2g
public import CFSG.GH74.GLS.C3.Layer2.L5C3
public import CFSG.GH74.GLS.C3.Layer2.L5C3b

public section

namespace CFSG.GH74.GLS

open CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.L5

theorem case48Facts
    : Case48Facts Sh2 inc where
  c1 := c1facts
  c2 := c1facts2
  rec1 := fun S [Group S] [Finite S] ι ρ hc hi h1 h2 h3 h4 => rec1 S ι ρ hc hi h1 h2 h3 h4
  sh2 := sh2_contract
  aut1 := fun γ r hr => aut1_of_e16 sh1_E16_unique γ r hr
  e16_1 := sh1_E16_unique
  noCHat := sh1_S0_no_cHat
  notge := sh0_R1_not_ge
  engine0 := fun E hE a b ha haa hbb hab =>
    mem_R1subP.2 (engine0 hE a b (mem_R1subP.1 ha) haa hbb hab)
  engine1 := fun E hE hR => engine1 hE hR

theorem s_case48
    : S_Case48 := s_case48_of_facts case48Facts

theorem s_prop46_proved
    : S_Prop46 := S_Prop46_of_case48 s_case48

theorem s_layerII_proved
    : S_layerII := s_layerII_of_case48 s_case48

end CFSG.GH74.GLS
