module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylUArg

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup

theorem weylModel : WeylModel where
  card_wE8 := card_wE8
  card_wPlus := card_wPlus
  refl_mem _ hr := refl_mem hr
  sZero_mem := sZero_mem_wE8
  sZero_not_mem := sZero_not_mem_wPlus
  sZero_sq := sZero_mul_self
  zPerm_mem := zPerm_mem_wPlus
  zPerm_ne_one := zPerm_ne_one
  zPerm_sq := zPerm_mul_self
  zPerm_comm := zPerm_comm
  commutator_eq := commutator_wE8
  perfect := commutator_wPlus
  centralizer_wPlus _ hw hc := centralizer_wPlus hw hc
  mem_center _ := mem_center_wPlus
  card_center := card_center_wPlus
  lieModel := lieModel_wPlus_quotient
  sq_eq_zPerm _ hw h := mem_wPlus_of_mul_self_eq_zPerm hw h
  doubleCover := exists_mulEquiv_wPlus

theorem weylAut : WeylAut where
  conj := exists_conj_eq
  card_mulAut := card_mulAut_wPlus
  foursGroup := foursGroupCondition_wPlus

theorem weylSylow : WeylSylow where
  tSub_le := tSub_le_wE8
  tPlusSub_eq := tPlusSub_eq_inf
  card_tSub := card_tSub
  card_tPlusSub := card_tPlusSub
  eSub_le := eSub_le_tPlusSub
  e1Sub_le := e1Sub_le_tSub
  e1PlusSub_le := e1PlusSub_le_tPlusSub
  center_tSub _ hx hc := center_tSub hx hc
  center_tPlusSub _ hx hc := center_tPlusSub hx hc
  centralizer_eSub _ hw hc := centralizer_eSub hw hc
  centralizer_e1Sub _ hw hc := centralizer_e1Sub hw hc
  centralizer_e1PlusSub _ hw hc := centralizer_e1PlusSub hw hc
  uPrimeSub_le := uPrimeSub_le_tPlusSub
  centralizer_uPrimeSub _ ht hc := centralizer_uPrimeSub_spec ht hc

theorem e1PlusSub_ne_eSub' : e1PlusSub ≠ eSub := by
  intro h
  have hv : frameE 0 + frameE 2 ∈ evenSub := frameE_add_mem 0 2
  have hm : frameElt (frameE 0 + frameE 2) ∈ eSub := h ▸ mem_e1PlusSub.2 ⟨_, hv, rfl⟩
  rw [frameElt_add, frameElt_even_eq 0 (by decide), frameElt_even_eq 2 (by decide),
    ← permMat_mul, permMat_mem_eSub_iff] at hm
  exact absurd hm (by decide)

theorem weylAbelian : WeylAbelian where
  abelian_tPlus := abelian_tPlus_spec
  abelian_t := abelian_t_spec
  card_eSub := card_eSub
  card_e1Sub := card_e1Sub
  card_e1PlusSub := card_e1PlusSub
  card_uPrimeSub := card_uPrimeSub
  sq_eSub e he := by
    obtain ⟨v, hv, rfl⟩ := mem_eSub.1 he
    exact signPerm_mul_self hv
  sq_e1Sub e he := by
    obtain ⟨v, rfl⟩ := mem_e1Sub.1 he
    exact frameElt_mul_self v
  comm_e1Sub _ ha _ hb := e1Sub_comm ha hb
  comm_uPrimeSub := uPrimeSub_comm
  not_sq_uPrimeSub := not_sq_uPrimeSub
  e1PlusSub_ne_eSub := e1PlusSub_ne_eSub'

theorem weylNormalizers : WeylNormalizers where
  normalizer_eSub _ hw hn := normalizer_eSub_spec hw hn
  permMat_mem σ := ⟨permMat_mem_wE8 σ, permMat_mem_normalizer σ,
    fun _ hv => permMat_conj_signPerm σ hv⟩
  permMat_mem_wPlus := permMat_mem_wPlus_iff
  card_normalizer_eSub := card_normalizer_eSub
  card_normalizer_eSub_plus := card_normalizer_eSub_plus
  normalizer_e1Sub _ hw hn := normalizer_e1Sub_action hw hn
  frameAut_realized _ hσ := frameAut_realized hσ
  normalizer_e1PlusSub _ hw := normalizer_e1PlusSub_iff hw
  card_normalizer_e1Sub := card_normalizer_e1Sub
  card_normalizer_e1Sub_plus := card_normalizer_e1Sub_plus

theorem weylInvolutions : WeylInvolutions where
  conj_e1Sub _ hx hxx := conj_e1Sub hx hxx
  conj_e1PlusSub _ hx hxx := conj_e1PlusSub hx hxx
  frame_conj_eSub _ _ h := frame_conj_eSub_spec h
  xPlane_eq := xPlane_eq_frameElt
  plane_conj _ hB := exists_conj_plane hB

theorem weylUArg : WeylUArg where
  uSub_le_eSub := uSub_le_eSub
  uSub_le_e1Sub := uSub_le_e1Sub
  card_uSub := card_uSub
  zPerm_mem := zPerm_mem_uSub
  xPlane_mem := xPlane_mem_uSub
  normal _ ht _ hu := uSub_normal ht hu
  unique := uSub_unique
  centralizer_iff _ ht := centralizer_iff_uSub ht
  card_cT := card_cT
  e1Sub_le := e1Sub_le_centralizer_xPlane
  center_cT _ hc := center_cT_spec hc
  center_mod _ hc := ⟨center_mod_spec hc, fun h => center_mod_rev h⟩
  comm_02 := comm_02_spec
  comm_46 := comm_46_spec
  comm_0246 := comm_0246_spec
  inf_uSub _ hg := inf_uSub_spec hg

theorem weylPackage : WeylPackage where
  model := weylModel
  aut := weylAut
  coords := weylCoords
  sylow := weylSylow
  abelian := weylAbelian
  normalizers := weylNormalizers
  involutions := weylInvolutions
  uArg := weylUArg

end CFSG.EvenSmallLie.OmegaEight.Weyl
