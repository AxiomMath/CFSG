module

public import CFSG.GH74.GLS.C3.Layer1.St1P14Rank
public import CFSG.GH74.GLS.C3.Layer1.St1PumpH3
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Out13Top

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Glue
  CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.P14

theorem hasL2Model_gt_three {K : Type} [Group K] (h : HasL2Model K Odd) :
    HasL2Model K (fun q => Odd q ∧ 3 < q) := by
  obtain ⟨p, f, hp, hf, hq, hL⟩ := h
  refine ⟨p, f, hp, hf, ⟨hq, ?_⟩, hL⟩
  rcases hL with ⟨-, hadm, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
    have h2 : (2, p ^ f) ≠ (2, 3) := hadm.2.2.2.2
    have h3 : p ^ f ≠ 3 := fun h => h2 (by rw [h])
    have h4 : (p ^ f) % 2 = 1 := Nat.odd_iff.1 hq
    omega
  all_goals exact absurd h0 (by norm_num)

theorem b_prop14_h1_of_leaves
    (hL34 : B_gen4_noL34_elem)
    (hIV3 : ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeaf x Kb)
    (hIV3A7 : ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeafA7 x Kb) :
    B_prop14_h1 := by
  intro G _ _ hGc x K hpair hU2 hrk1
  by_contra hlt
  have hlt' : pRank 2 ↥(centralizer ({x} : Set G)) < 4 := not_le.1 hlt
  have hx2 : orderOf x = 2 := hpair.1
  have h3 : 3 ≤ pRank 2 ↥(centralizer ({x} : Set G)) :=
    C3.Layer1.PumpH1.three_le_pRank_centralizer hL34 hGc.gen4 hpair hU2
  have hrk3 : pRank 2 ↥(centralizer ({x} : Set G)) = 3 := by omega
  have hr4 : pRank 2 G = 4 := hGc.pRank_eq_four
  have hc : CFSG.IsComponent (bar x K) := isComponent_bar hpair.2
  obtain ⟨e⟩ := kBar_equiv_bar hpair.2
  have h13 : Sec13.Prop12_1_nonE8 :=
    Sec13.prop12_1_nonE8_of_facts Bg.TwoGroups.Bridge13.sec13_ig_9_16
      Bg.TwoGroups.Bridge13.sec13_ig_10_31 Sec13.ig_15_15_sec13 Bg.ig_16_20
      Bg.TwoGroups.Bridge13.sec13_iv2_2_18 Bg.TwoGroups.Bridge13.sec13_iv2_2_7
  have hnonab : ∀ S : Subgroup G, IsSylow2In S ⊤ → ¬ (Sec12.IsElemAb2 S ∧ Nat.card S = 8) :=
    fun S hS hS8 => not_sylow_card_eight hS hS8.2 hr4
  rcases hU2.2 with hmod | hA7 | hL34'
  ·
    have hmodel : HasL2Model ↥(bar x K) (fun q => Odd q ∧ 3 < q) :=
      TwoThin.hasL2Model_of_mulEquiv e (hasL2Model_gt_three hmod)
    have hnorm : (bar x K).Normal := normal_of_hasL2Model hrk3.le hc hmodel
    have c : Stage1.Thm6.Glue.Conf12B G x (bar x K) :=
      ⟨hGc.kproper.1, hGc.kproper.2.1, hx2, hc, hnorm, hrk3⟩
    obtain ⟨x', T, V, S, a, b, y, o⟩ :=
      out13_of_conf12B_L2 (ivkL2Facts_of_proved IVK.ivk_1_2_general IVK.ivk_1_3f_c) c
        (isL2Model_of_hasL2Model hmodel) (hIV3 G hGc x (bar x K)) h13 hnonab
    have := pRank_le_three_of_M12Data o.sylow o.data
    omega
  ·
    have hA7' : Nonempty (↥(bar x K) ≃* alternatingGroup (Fin 7)) := by
      obtain ⟨f⟩ := hA7
      exact ⟨e.symm.trans f⟩
    have hnorm : (bar x K).Normal := normal_of_isA7Model hrk3.le hc hA7'
    have c : Stage1.Thm6.Glue.Conf12B G x (bar x K) :=
      ⟨hGc.kproper.1, hGc.kproper.2.1, hx2, hc, hnorm, hrk3⟩
    obtain ⟨x', T, V, S, a, b, y, o⟩ :=
      out13_of_conf12B_A7 (ivkA7Facts_of_proved IVK.ivk_1_1f) c hA7' (hIV3A7 G hGc x (bar x K))
        h13 hnonab
    have := pRank_le_three_of_M12Data o.sylow o.data
    omega
  · exact hL34 G hGc.gen4 x K hx2 hpair.2 hL34'

end CFSG.GH74.GLS
