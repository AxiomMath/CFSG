module

public import CFSG.GH74.GLS.C3.Layer1.St1EndN710
public import CFSG.GH74.GLS.C3.Layer1.St1EndNSimple

public section

namespace CFSG.GH74.GLS

theorem b_st1_prop71_endB_of_simple
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (hB2 : B_B2) (hS : B_st1_prop71_lemma711_simple) :
    B_st1_prop71_endB :=
  b_st1_prop71_endB_of_lemma711 h102 h14 hL34 hadd hB2 (b_st1_prop71_lemma711_of_simple hS)

end CFSG.GH74.GLS
