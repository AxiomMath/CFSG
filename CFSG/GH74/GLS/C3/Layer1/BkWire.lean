module

public import CFSG.GH74.GLS.C3.Layer1.BkPgl3
public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk102L

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open CFSG.GH74.GLS

theorem b_ivk_10_2a_proof :
    B_ivk_10_2a :=
  b_ivk_10_2a_of IVK.Proofs2.b_ivk_10_2L

theorem b_prop91_PGL_of'
    (h92 : B_lemma92) (hK : B_pgl_K) : B_prop91_PGL :=
  b_prop91_PGL_of h92 IVK.Proofs2.b_ivk_10_2L hK

end CFSG.GH74.GLS.C3.Layer1.Bk
