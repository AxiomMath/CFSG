module

public import CFSG.GH74.GLS.C3.Layer1.St1P77L29
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk61L29

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.GH74.GLS

theorem b_ivk_6_1_L29 :
    B_ivk_6_1_L29 := by
  intro G _ _ _ x K hpair hL29 hC1 A hAN hA hcard hxA
  exact le_sup_of_le_right (b_ivk_6_1_L29_aux hpair hL29 hC1 hAN hA hcard hxA)

end CFSG.GH74.GLS.IVK.Proofs2
