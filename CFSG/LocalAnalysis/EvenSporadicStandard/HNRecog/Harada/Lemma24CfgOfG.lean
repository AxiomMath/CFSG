module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24CfgFP
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24CfgT
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Cfg

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {t z b z₁ : G} {S Eg T T' W0 : Subgroup G} {ι : Elem2 6 →* G}
  {a : G}

theorem cfg24_of_G [Finite G] (hD : HData G t z b z₁ S Eg T T' W0 ι) (hD3 : HData3 G t z z₁)
    (hconj : ∀ v, IsConj t (coordElt ι v) ↔ qp v = 1) (h : Setting24 ι a)
    (hat : a ∈ centralizer ({t} : Set G)) (ha3 : orderOf a = 3) :
    Cfg24 (Y24 a) (aY a) (tY hat) (τY a t) (FY ι a) (PY ι a) :=
  { a_central := aY_mem_center a
    orderOf_a := orderOf_aY ha3
    t_sq := tY_sq hat hD.t_sq
    t_ne_one := tY_ne_one hat hD.core.t_ne_one
    τ_t := IsConj.refl t
    τ_conj := τY_conj a t
    τ_fusion := τY_fusion hD3 hat ha3
    F_perfect := FY_perfect h
    F_inf := FY_inf h
    F_center := FY_center h
    P_le := PY_le_FY h
    P_card := card_PY h
    P_A8 := isA8Type_PY h
    Y_sylow := card_two_subgroup_le_Y h hD3 hD.ι_tv hat ha3 hconj
    card_C := card_centralizer_tY hD3 hat ha3
    odd_normal := odd_normal_Y hD3 hat ha3
    card_tT := card_tInvolutions_Y hD hD3 hconj hat ha3
    perfect60 := perfect60_Y hD3 hat ha3
    W_comm := W_comm_Y hD hD3 hconj hat ha3 }

end CFSG.EvenSporadicStandard.HNRecog.Harada
