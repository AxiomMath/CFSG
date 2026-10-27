module

public import CFSG.GH74.GLS.Bg.Iii2.L41
public import CFSG.GH74.GLS.Bg.Iii2.CM
public import CFSG.GH74.GLS.Bg.Iii2.II443d
public import CFSG.GH74.GLS.Bg.Iii2.Fusion
public import CFSG.GH74.GLS.Bg.Iii2.Ext
public import CFSG.GH74.GLS.Bg.Iii2.Tail

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec6

theorem b_iii2_G4 (h44 : II4_44) (hAut : II4_Aut) (hquat : II4_4_quat) : B_iii2_G4 :=
  b_iii2_G4_of (l41_of h44) (extP_of pu_of cm_of (ii4_43d_of h44 hAut) hquat)
    (tailP_of hquat h44 cm_of fusionKlein_of)

end CFSG.GH74.GLS.Bg.Iii2
