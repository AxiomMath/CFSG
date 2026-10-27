module

public import CFSG.GH74.GLS.C3.Layer1.BkTop3
public import CFSG.GH74.GLS.C3.Layer1.BkL113aTop
public import CFSG.GH74.GLS.C3.Layer1.BkD6Top

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open CFSG.GH74.GLS

theorem b_lemma113a_of_small
    (hs : B_ivk_6_small) (hrest : B_lemma113a_rest) : B_lemma113a :=
  b_lemma113a_of_rest (s_lemma112_of_small hs) hrest

theorem b_lemma113_d6_of_small
    (hs : B_ivk_6_small) (hrest : B_lemma113a_rest) : B_lemma113_d6 :=
  b_lemma113_d6_proof (b_lemma113a_of_small hs hrest)

end CFSG.GH74.GLS.C3.Layer1.Bk
