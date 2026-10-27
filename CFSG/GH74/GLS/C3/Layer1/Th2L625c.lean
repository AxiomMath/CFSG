module

public import CFSG.GH74.GLS.C3.Layer1.Th2L625b
public import CFSG.GH74.GLS.C3.Layer1.Th2V2Core

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

@[expose] def B_lemma625c1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K : Subgroup G),
    IsV2StarTriple x y K → HasL2Model (kBar K) (fun q => q = 5) → pRank 2 ↥(CxK x K) = 2 →
      ∀ (v w : G) (H : Subgroup G), IsLocallyUnbalancing v w H →
        pRank 2 ↥(centralizer ({v, w} : Set G)) = 4 →
          HasL2Model (kBar H) (fun q => Odd q ∧ IsFM9 q)

@[expose] def B_lemma625c2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K : Subgroup G),
    IsV2StarTriple x y K → HasL2Model (kBar K) (fun q => q = 5) → pRank 2 ↥(CxK x K) = 2 →
      ∀ (v w : G) (H : Subgroup G), IsLocallyUnbalancing v w H →
        pRank 2 ↥(centralizer ({v, w} : Set G)) = 4 →
          HasL2Model (kBar H) (fun q => Odd q ∧ IsFM9 q) → pRank 2 ↥(CxK v H) = 2

@[expose] def B_625_rank : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K : Subgroup G),
    Is2TerminalU2Triple x y K → twoPartCard K = 4 → 2 ≤ pRank 2 ↥(CxK x K)

theorem exists_twoTerminalU2_pump
    (h610 : B_ig_6_10) (h720 : B_ivk_7_20) (h14 : B_prop14) (h103 : B_ivk_10_3)
    (hL34 : B_gen4_noL34_elem) (hL29 : B_inC2_L29)
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x : G} {K : Subgroup G} (hpair : IsIL2Pair x K)
    (hU2 : InU2 (kBar K)) (hnC2 : ¬ InC2 (kBar K)) :
    ∃ (x' y' : G) (K' : Subgroup G), Is2TerminalU2Triple x' y' K' ∧ InU2 (kBar K') ∧
      ¬ InC2 (kBar K') := by
  have hr4 : pRank 2 G = 4 := hG.pRank_eq_four
  have h4 := h14 G hG x K hpair hU2
  have hILo : IsILo 2 x K := ⟨hpair.1, by simp only [oBound, ite_true]; omega, hpair.2⟩
  obtain ⟨x', K', hlong, hterm⟩ := h610 G hG.kproper (by rw [hr4]; norm_num) x K hILo
  obtain ⟨hU2', hbad'⟩ := h720 G hG x K x' K' hpair hU2 hnC2 hlong
  have hILo' : IsILo 2 x' K' := hlong.isILo_right
  have hpair' : IsIL2Pair x' K' := ⟨hILo'.1, hILo'.2.2⟩
  have hstar : IsStar2 x' :=
    ⟨hILo'.1, le_antisymm (Bg.pRank_subgroup_le one_lt_two _)
      (by rw [hr4]; exact h14 G hG x' K' hpair' hU2')⟩
  obtain ⟨y, hy⟩ := h103 G hG x' K' hpair' hU2' hbad'
  refine ⟨x', y, K', ⟨hy, hterm, hstar, ?_, ?_⟩, hU2', hbad'⟩
  · intro hl34
    exfalso
    have hc := inU2_center hU2'
    exact hL34 G hG.gen4 x' K' hpair'.1 hpair'.2 ⟨hl34, hc.1, hc.2⟩
  · intro hl29
    exact absurd (hL29 _ hU2' hl29) hbad'

theorem b_lemma625c1_of
    (h610 : B_ig_6_10) (h720 : B_ivk_7_20) (h14 : B_prop14) (h103 : B_ivk_10_3)
    (hL34 : B_gen4_noL34_elem) (hL29 : B_inC2_L29) (h102 : B_ivk_10_2)
    (hfm : Th2.L625.ClassFM9) (hfour : B_thm1_four) (hrank : B_625_rank) : B_lemma625c1 := by
  intro G _ _ hG x y K hV hK5 hCx v w H hlu hrk
  have h625a : ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K : Subgroup G),
      IsV2StarTriple x y K → HasL2Model (kBar K) (fun q => q = 5) →
        ∀ (v w : G) (H : Subgroup G), IsV2Triple v w H → HasL2Model (kBar H) (fun q => q = 5) :=
    fun G _ _ hG x y K hV hK5 v w H hv => Th2.L625.lemma625a_of h102 hL34 hfm hG hV hK5 hv
  by_contra hnot
  have hU2H : InU2 (kBar H) := h102 G hG v w H hlu
  have hno : ¬ IsL34Quotient (kBar H) := fun hl34 =>
    hL34 G hG.gen4 v H hlu.1.1 hlu.1.2 ⟨hl34, (inU2_center hU2H).1, (inU2_center hU2H).2⟩
  have hnC2 : ¬ InC2 (kBar H) := fun hC2 => by
    obtain ⟨p, f, hp, hf, hfm', hL⟩ := Th2.L625.hasL2Model_fm9_of_inC2 hfm hG hlu hU2H hno hC2
    exact hnot ⟨p, f, hp, hf, ⟨isFM9_odd hfm', hfm'⟩, hL⟩
  obtain ⟨v', w', H', hU', hU2', hnC2'⟩ :=
    exists_twoTerminalU2_pump h610 h720 h14 h103 hL34 hL29 hG hlu.1 hU2H hnC2
  have h4 : twoPartCard H' = 4 := Th2.L625.lemma625b_of hfour h102 hL34 h14 hG hV hK5 hU'
  have hr : 2 ≤ pRank 2 ↥(CxK v' H') := hrank G hG v' w' H' hU' h4
  have hV' : IsV2Triple v' w' H' := ⟨hU'.1, hU'.2.1, Or.inl hr, fun _ => hU'⟩
  have h5 : HasL2Model (kBar H') (fun q => q = 5) := h625a G hG x y K hV hK5 v' w' H' hV'
  obtain ⟨p, f, hp, hf, h5', hL⟩ := h5
  exact hnC2' (Th2.L625.inC2_of_l2_fm9 hU2' ⟨p, f, hp, hf, h5' ▸ Th2Tstar.isFM9_five, hL⟩)

open CFSG.GH74.GLS.Th2 in
theorem b_prop624b_of_c1 (hunb : B_prop61b_unb) (h625c1 : B_lemma625c1) : B_prop624b := by
  intro G _ _ hG x y K T S h h5 hQ2 B hB
  by_contra hweak
  obtain ⟨b, d, J, hb, hd, hunbal, hJ⟩ := hunb G hG B hB hweak
  have hCx : pRank 2 ↥(CxK x K) = 2 := by
    have := pRank_eq_of_isSylowOf h.sylow_Q
    omega
  have hrank := (show IsEStarUnbal b d J from ⟨hunbal, B, hB, hb, hd⟩).pRank_centralizer
    hG.pRank_eq_four
  have hL2 := h625c1 G hG x y K h.v2ss.1 h5 hCx b d J hunbal.isLocallyUnbalancing hrank
  rcases hJ with hA7 | hL2'
  · exact not_nonempty_A7_of_hasL2Model hL2 hA7
  · obtain ⟨q, hq1, hq2⟩ := Th2.Bal.exists_eq_of_hasL2Model hL2 hL2' (fun q hq => hq.1)
      (fun q hq => hq.1)
    exact hq2.2 hq1.2

end CFSG.GH74.GLS
