module

public import CFSG.GH74.GLS.C3.Layer1.BkTop
public import CFSG.GH74.GLS.C3.Layer1.BkTop2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Big

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open CFSG.GH74.GLS

theorem b_ivk_6_of_small
    (hs : B_ivk_6_small) : B_ivk_6 :=
  b_ivk_6_of_parts hs IVK.Proofs2.b_ivk_6_big

theorem b_lemma92_of_small
    (hs : B_ivk_6_small) : B_lemma92 :=
  b_lemma92_of_ivk6 (b_ivk_6_of_small hs)

theorem b_prop91_PGL_of_small
    (hs : B_ivk_6_small) : B_prop91_PGL :=
  b_prop91_PGL_proof (b_lemma92_of_small hs)

theorem s_lemma112_of_small
    (hs : B_ivk_6_small) : S_lemma112 :=
  s_lemma112_proof (b_lemma92_of_small hs)

theorem b_lemma113_L27_of_small
    (hs : B_ivk_6_small) : B_lemma113_L27 :=
  b_lemma113_L27_proof (b_lemma92_of_small hs)

end CFSG.GH74.GLS.C3.Layer1.Bk
