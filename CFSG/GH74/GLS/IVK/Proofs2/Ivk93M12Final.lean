module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Der
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12FAlt
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12FSpor
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12FL2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12FL3U3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12FExc
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12FSp4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12LU
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Bender
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12L28
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12J1
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Ree
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12L34
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abD4Native
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Lift

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

theorem ivk93M12Leaves_proved :
    Ivk93M12Leaves := by
  exact
    { alt := ivk93m12_alt
      m11 := ivk93m12_m11
      m22 := ivk93m12_m22
      m23 := ivk93m12_m23
      j1 := ivk93m12_j1
      j2 := ivk93m12_j2
      j3 := ivk93m12_j3
      mcl := ivk93m12_mcl
      ly := ivk93m12_ly
      l2 := ivk93m12_l2
      l3 := ivk93m12_l3
      u3 := ivk93m12_u3
      sp4 := ivk93m12_sp4
      g2 := ivk93m12_g2
      d4 := ivk93m12_d4
      l4 := ivk93m12_l4
      u4 := ivk93m12_u4
      l5 := ivk93m12_l5
      u5 := ivk93m12_u5
      ree := ivk93m12_ree
      l28 := ivk93m12_l28
      l216 := ivk93m12_l216
      l34 := ivk93m12_l34
      u34 := ivk93m12_u34
      sz8 := ivk93m12_sz8 }

theorem ivk93M12J_proved :
    Ivk93M12J :=
  ivk93M12J_of_leaves ivk93M12Der_proved ivk93M12Leaves_proved

theorem ivk93KindM12_proved :
    Ivk93KindM12 :=
  ivk93KindM12_of_J ivk93M12J_proved

end CFSG.GH74.GLS.IVK.Proofs2
