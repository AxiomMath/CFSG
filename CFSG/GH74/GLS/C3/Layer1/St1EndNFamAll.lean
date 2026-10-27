module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamSmall
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamSpor
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamExc
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamAlt
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamL34
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFinal

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

@[expose] def B_st1_prop71_lemma711_oddClassical : Prop :=
  Lem711Empty fun X _ => IVK.OddClassicalSix X

theorem lem711Leaves_of_oddClassical
    (ho : B_st1_prop71_lemma711_oddClassical) : Lem711Leaves where
  alt := lem711_alt
  m11 := lem711_m11
  m12 := lem711_m12
  m22 := lem711_m22
  m23 := lem711_m23
  j1 := lem711_j1
  j2 := lem711_j2
  j3 := lem711_j3
  mcl := lem711_mcl
  ly := lem711_ly
  l2 := lem711_l2
  oddClassical := ho
  g2 := lem711_g2
  d4 := lem711_d4
  ree := lem711_ree
  l28 := lem711_l28
  l216 := lem711_l216
  l34 := lem711_l34
  u34 := lem711_u34
  sz8 := lem711_sz8

theorem b_st1_prop71_lemma711_simple_of_oddClassical
    (ho : B_st1_prop71_lemma711_oddClassical) : B_st1_prop71_lemma711_simple :=
  b_st1_prop71_lemma711_simple_of_leaves (lem711Leaves_of_oddClassical ho)

theorem b_st1_prop71_endB_of_oddClassical
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (hB2 : B_B2) (ho : B_st1_prop71_lemma711_oddClassical) :
    B_st1_prop71_endB :=
  b_st1_prop71_endB_of_simple h102 h14 hL34 hadd hB2 (b_st1_prop71_lemma711_simple_of_oddClassical ho)

end CFSG.GH74.GLS
