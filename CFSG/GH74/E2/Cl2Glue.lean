module

public import CFSG.GH74.E2.Cl2
public import CFSG.GH74.E2.CaseIINoComp

public section

namespace CFSG.GH74.E2

theorem cl2Statement_of_wrap : Cl2Statement :=
  fun _ _ _ _ _ _ φ hX _ hP hinj hcomm hpow hcard hfix x y z =>
    gen4_bgroup_class_le_two φ hX hP hinj hcomm hpow hcard hfix x y z

end CFSG.GH74.E2
