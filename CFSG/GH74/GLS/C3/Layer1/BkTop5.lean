module

public import CFSG.GH74.GLS.C3.Layer1.BkTop4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Small

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open CFSG.GH74.GLS

theorem b_lemma92_proof :
    B_lemma92 :=
  b_lemma92_of_small IVK.Proofs2.b_ivk_6_small

theorem b_prop91_PGL_proof' :
    B_prop91_PGL :=
  b_prop91_PGL_of_small IVK.Proofs2.b_ivk_6_small

theorem b_lemma113a_of_rest'
    (hrest : B_lemma113a_rest) : B_lemma113a :=
  b_lemma113a_of_small IVK.Proofs2.b_ivk_6_small hrest

theorem b_lemma113_L27_proof' :
    B_lemma113_L27 :=
  b_lemma113_L27_of_small IVK.Proofs2.b_ivk_6_small

theorem b_lemma113_d6_of_rest'
    (hrest : B_lemma113a_rest) : B_lemma113_d6 :=
  b_lemma113_d6_of_small IVK.Proofs2.b_ivk_6_small hrest

end CFSG.GH74.GLS.C3.Layer1.Bk
