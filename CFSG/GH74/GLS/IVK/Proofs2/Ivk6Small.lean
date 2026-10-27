module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6SmallL2
public import CFSG.GH74.GLS.IVK.Proofs2.A7Small

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

theorem b_ivk_6_small :
    CFSG.GH74.GLS.C3.Layer1.Bk.B_ivk_6_small := by
  intro K _ _ W hshape hW2 hWr hΓ
  rcases hshape with hL | hA
  · exact b_ivk_6_small_L2 W hL hW2 hWr hΓ
  · exact A7Fin.b_ivk_6_small_A7 W hA hW2 hWr hΓ

theorem b_ivk_6 :
    CFSG.GH74.GLS.C3.Layer1.Bk.B_ivk_6 :=
  CFSG.GH74.GLS.C3.Layer1.Bk.b_ivk_6_of_parts b_ivk_6_small b_ivk_6_big

end CFSG.GH74.GLS.IVK.Proofs2
