module

public import CFSG.GH74.GLS.C3.Layer1.St1C2L29
public import CFSG.GH74.GLS.C3.Layer1.St1PumpClass
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.GLS.C3.Layer1.Th2BalL2Local
public import CFSG.GH74.GLS.C3.Layer1.Th2BalRows

public section

namespace CFSG.GH74.GLS.Th2.L625

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1
open CFSG.Open (ordA)

theorem inC2_of_l2_fm9
    {K : Type} [Group K] (hU2 : InU2 K) (hL : HasL2Model K IsFM9) : InC2 K := by
  obtain ⟨p, f, hp, hf, hfm, hL⟩ := hL
  obtain ⟨hfin, -, hs⟩ := CFSG.LieType.Catalog.lieModel_finite_simple K _ _ p f hL
  have hq : IsQuasisimple K := hU2.1
  have hc : center K = ⊥ := center_eq_bot_of_simple_quasisimple hs hq
  have hp2 : pCore 2 K = ⊥ := pCore_eq_bot_of_simple hs hc
  refine ⟨hq, hc.trans hp2.symm, ?_, ?_⟩
  · have e : K ⧸ center K ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    exact E2.simpleInC2_of_mulEquiv e.symm (Generic.simpleInC2_of_fm9 hs hp hf hfm hL)
  · exact not_excludedFromC2_of_center_eq_bot hc

section Orders

theorem card_of_l2_five {J : Type} [Group J] (hJ : HasL2Model J (fun q => q = 5)) :
    Nat.card J = 60 := by
  obtain ⟨p, f, hp, hf, h5, hL⟩ := hJ
  rw [CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hL, h5]
  have := PumpClass.ordA_one_odd 2
  simpa using this

theorem le_ordA_of_odd_of_seven_le {q : ℕ} (hq : Odd q) (h7 : 7 ≤ q) : 168 ≤ ordA 1 q := by
  obtain ⟨k, rfl⟩ := hq
  rw [PumpClass.ordA_one_odd]
  have hk : 3 ≤ k := by omega
  calc 168 = 2 * 3 * (3 + 1) * (2 * 3 + 1) := by norm_num
    _ ≤ 2 * k * (k + 1) * (2 * k + 1) := by gcongr

end Orders

section Order

theorem u2Succ_A7 {H J : Type} [Group H] [Group J] (hH : InU2 H) (hJ : InU2 J)
    (hA7 : Nonempty (H ≃* alternatingGroup (Fin 7))) (hJ5 : HasL2Model J (fun q => q = 5)) :
    U2Succ H J := by
  refine ⟨hH, hJ, Or.inl ⟨hA7, ?_⟩⟩
  rintro ⟨e⟩
  have h60 := card_of_l2_five hJ5
  have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  rw [Nat.card_congr e.toEquiv, h7] at h60
  omega

end Order

section Main

variable {G : Type} [Group G] [Finite G]

@[expose] def ClassFM9 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], TwoThin.Gen4Comp L → InC2 L → InU2 L →
    ¬ IsL34Quotient L → HasL2Model L IsFM9

theorem hasL2Model_fm9_of_inC2 (hfm : ClassFM9) (hG : C3Hyp G) {v w : G} {H : Subgroup G}
    (hlu : IsLocallyUnbalancing v w H) (hU2 : InU2 (kBar H)) (hno : ¬ IsL34Quotient (kBar H))
    (hC2 : InC2 (kBar H)) : HasL2Model (kBar H) IsFM9 := by
  obtain ⟨eb⟩ := PumpCalc.kBar_equiv_bar hlu.1.2
  have hP : TwoThin.Gen4Comp ↥(PumpCalc.bar v H) :=
    TwoThin.gen4Comp_of_gen4Cen (TwoThin.gen4Cen_barQ hG.gen4 hlu.1.1) _
  have hL2b : HasL2Model ↥(PumpCalc.bar v H) IsFM9 :=
    hfm _ hP (CFSG.GH74.E2.inC2_of_mulEquiv eb hC2) (inU2_of_mulEquiv eb hU2)
      (fun hl => hno (TwoThin.isL34Quotient_of_mulEquiv eb.symm hl))
  exact TwoThin.hasL2Model_of_mulEquiv eb.symm hL2b

theorem lemma625a_of
    (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (hfm : ClassFM9) (hG : C3Hyp G)
    {x y : G} {K : Subgroup G} (hV : IsV2StarTriple x y K)
    (hK5 : HasL2Model (kBar K) (fun q => q = 5)) {v w : G} {H : Subgroup G}
    (hv : IsV2Triple v w H) : HasL2Model (kBar H) (fun q => q = 5) := by
  have hVT : IsV2Triple x y K := hV.1.1.1.1
  have hmax : ∀ (x' y' : G) (K' : Subgroup G), IsV2Triple x' y' K' →
      ¬ U2Succ (kBar K') (kBar K) := hV.1.1.1.2
  have hlu : IsLocallyUnbalancing v w H := hv.1
  have hU2H : InU2 (kBar H) := h102 G hG v w H hlu
  have hU2K : InU2 (kBar K) := h102 G hG x y K hVT.1
  have hC2K : InC2 (kBar K) := by
    obtain ⟨p, f, hp, hf, h5, hL⟩ := hK5
    exact inC2_of_l2_fm9 hU2K ⟨p, f, hp, hf, h5 ▸ Th2Tstar.isFM9_five, hL⟩
  have hno : ¬ IsL34Quotient (kBar H) := fun hl34 =>
    hL34 G hG.gen4 v H hlu.1.1 hlu.1.2 ⟨hl34, (inU2_center hU2H).1, (inU2_center hU2H).2⟩
  by_contra hnot
  apply hmax v w H hv
  rcases hU2H.2 with ⟨p, f, hp, hf, hodd, hL⟩ | hA7 | ⟨hl34, hel, hcard⟩
  · obtain ⟨F, _, _, e0, hF, hcF⟩ := Th2.Bal.exists_l2Field_of_lieModel hodd hL
    have hq3 : 3 < p ^ f := hcF ▸ hF.2
    have h5 : p ^ f ≠ 5 := fun h => hnot ⟨p, f, hp, hf, h, hL⟩
    have h7 : 7 ≤ p ^ f := by
      obtain ⟨k, hk⟩ := hodd
      omega
    by_cases hfm' : IsFM9 (p ^ f)
    · have hC2H : InC2 (kBar H) := inC2_of_l2_fm9 hU2H ⟨p, f, hp, hf, hfm', hL⟩
      refine ⟨hU2H, hU2K, Or.inr (Or.inr ⟨Or.inl ⟨hC2H, hC2K⟩, ?_⟩)⟩
      rw [card_of_l2_five hK5, CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hL]
      have := le_ordA_of_odd_of_seven_le hodd h7
      simpa using this.trans_lt' (by norm_num : 60 < 168)
    · refine ⟨hU2H, hU2K, Or.inr (Or.inl ⟨?_, hC2K⟩)⟩
      intro hC2H
      obtain ⟨p', f', hp', hf', hfm'', hL'⟩ := hasL2Model_fm9_of_inC2 hfm hG hlu hU2H hno hC2H
      have hc1 := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hL
      have hc2 := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hL'
      have heq : p ^ f = p' ^ f' :=
        Th2.Bal.eq_of_ordA_one_eq hodd (isFM9_odd hfm'') (by simpa using hc1.symm.trans hc2)
      exact hfm' (heq ▸ hfm'')
  · exact u2Succ_A7 hU2H hU2K hA7 hK5
  · exact absurd hl34 hno

end Main

end CFSG.GH74.GLS.Th2.L625

