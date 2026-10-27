module

public import CFSG.GH74.GLS.C3.Layer1.BkL114A7
public import CFSG.GH74.GLS.C3.Layer1.Back112Main
public import CFSG.GH74.GLS.C3.Layer1.Back113
public import CFSG.GH74.GLS.C3.Layer1.BackAssemble
public import CFSG.GH74.GLS.C3.Layer1.BackMain

public section

namespace CFSG.GH74.GLS

theorem s_back_of_all_leaves5
    (h81 : B_iv2_8_1) (h92 : B_lemma92) (h102 : B_ivk_10_2)
    (h102a : B_ivk_10_2a) (hL34 : B_gen4_noL34_elem) (hPGL : B_prop91_PGL) (ha : B_lemma113a)
    (hL27 : B_lemma113_L27) (hd : B_lemma113_d6) (hA : C3.Layer1.Bk.B_L114_fusion5)
    (hF : C3.Layer1.Bk.B_L114_final57) : S_back :=
  s_back_of (C3.Layer1.Back.s_prop91_of h81 h92 h102 h102a hL34 hPGL)
    (C3.Layer1.Back.s_lemma113_of (s_lemma112_of h81 h92 h102a) ha hL27 hd)
    (s_lemma114_of (C3.Layer1.Bk.b_lemma114_nonEven_of_leaves5 hA hF))

end CFSG.GH74.GLS
