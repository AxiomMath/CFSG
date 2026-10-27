module

public import CFSG.GH74.GLS.C3.Layer1.BkWire
public import CFSG.GH74.GLS.C3.Layer1.BkL27
public import CFSG.GH74.GLS.C3.Layer1.BkIv81
public import CFSG.GH74.GLS.C3.Layer1.Back112Main

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open CFSG.GH74.GLS

theorem s_lemma112_proof
    (h92 : B_lemma92) : S_lemma112 :=
  s_lemma112_of b_iv2_8_1_proof h92 b_ivk_10_2a_proof

theorem b_lemma113_L27_proof
    (h92 : B_lemma92) : B_lemma113_L27 :=
  b_lemma113_L27_of (s_lemma112_proof h92)

end CFSG.GH74.GLS.C3.Layer1.Bk
