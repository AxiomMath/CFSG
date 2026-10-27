module

public import CFSG.GH74.GLS.C3.Layer1.Th2L625Rank

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.GH74.GLS.C3.Layer1.PumpCalc

theorem no_u2_notC2

    (h610 : B_ig_6_10) (h720 : B_ivk_7_20) (h14 : B_prop14) (h103 : B_ivk_10_3)
    (hL34 : B_gen4_noL34_elem) (hL29 : B_inC2_L29) (h102 : B_ivk_10_2)
    (hfm : Th2.L625.ClassFM9) (hfour : B_thm1_four)
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x y : G} {K : Subgroup G}
    (hV : IsV2StarTriple x y K) (hK5 : HasL2Model (kBar K) (fun q => q = 5))
    {v : G} {L : Subgroup G} (hpair : IsIL2Pair v L)
    (hU2 : InU2 (kBar L)) : InC2 (kBar L) := by
  have h625a : ∀ (v w : G) (H : Subgroup G), IsV2Triple v w H → HasL2Model (kBar H) (fun q => q = 5) :=
    fun v w H hv => Th2.L625.lemma625a_of h102 hL34 hfm hG hV hK5 hv
  by_contra hnC2
  obtain ⟨v', w', H', hU', hU2', hnC2'⟩ :=
    exists_twoTerminalU2_pump h610 h720 h14 h103 hL34 hL29 hG hpair hU2 hnC2
  have h4 : twoPartCard H' = 4 := Th2.L625.lemma625b_of hfour h102 hL34 h14 hG hV hK5 hU'
  have hr : 2 ≤ pRank 2 ↥(CxK v' H') := b_625_rank_of h102 hL34 G hG v' w' H' hU' h4
  have hV' : IsV2Triple v' w' H' := ⟨hU'.1, hU'.2.1, Or.inl hr, fun _ => hU'⟩
  obtain ⟨p, f, hp, hf, h5', hL⟩ := h625a v' w' H' hV'
  exact hnC2' (Th2.L625.inC2_of_l2_fm9 hU2' ⟨p, f, hp, hf, h5' ▸ Th2Tstar.isFM9_five, hL⟩)

theorem inC2_of_pumpup_component

    (h610 : B_ig_6_10) (h720 : B_ivk_7_20) (h14 : B_prop14) (h103 : B_ivk_10_3)
    (hL34 : B_gen4_noL34_elem) (hL29 : B_inC2_L29) (h102 : B_ivk_10_2)
    (hfm : Th2.L625.ClassFM9) (hfour : B_thm1_four)
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x y : G} {K : Subgroup G}
    (hV : IsV2StarTriple x y K) (hK5 : HasL2Model (kBar K) (fun q => q = 5))
    {v : G} {L : Subgroup G} (hpair : IsIL2Pair v L) :
    InC2 (kBar L) := by
  have hlt2o : L2Sub G (fun K _ => InC2 K ∨ InU2 K) := hG.lt2o.2
  obtain ⟨e⟩ := kBar_equiv_bar hpair.2
  rcases hlt2o v hpair.1 (bar v L) (isComponent_bar hpair.2) with hC | hU
  · exact CFSG.GH74.E2.inC2_of_mulEquiv e.symm hC
  · exact no_u2_notC2 h610 h720 h14 h103 hL34 hL29 h102 hfm hfour hG hV hK5 hpair
      (inU2_of_mulEquiv e.symm hU)

end CFSG.GH74.GLS
