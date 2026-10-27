module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Final
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.A7Top
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.A7Facts
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Facts
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Main
public import CFSG.GH74.GLS.Stage1.Thm6.Adapters13
public import CFSG.GH74.GLS.Bg.TwoGroups.Bridge13
public import CFSG.GH74.GLS.Bg.Local.Prop1620

public section

namespace CFSG.GH74.GLS.Stage1.Thm6

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6.Sec12 CFSG.GH74.GLS.Stage1.Thm6.Sec12b
  CFSG.GH74.GLS.Stage1.Thm6.Glue

variable {G : Type} [Group G] [Finite G] {x : G}

theorem out13_of_kfacts {S T P Q Rd F U : Subgroup G} (hZ : IG_15_3) (hBur : IG_16_2)
    (hThomp : IG_15_15) (h13 : Sec13.Prop12_1_nonE8) (hk : KFacts x S T P Q Rd F U)
    (hIV3 : IV3_12_8c_sylow x S T P) (hnonab : ¬ (IsElemAb2 S ∧ Nat.card S = 8)) :
    ∃ (x' : G) (T' V S' : Subgroup G) (a b y : G), Sec13.Out13 G x' T' V S' a b y := by
  obtain ⟨V, -, hV⟩ := out12_of_kfacts hZ hBur hThomp hk hIV3 hnonab
  obtain ⟨S', a, b, y, o⟩ := h13 G x T V hV
  exact ⟨x, T, V, S', a, b, y, o⟩

theorem out13_of_conf12B_L2 (hIVK : IVKL2Facts) {Kb : Subgroup (CentralizerBar x)}
    (c : Conf12B G x Kb) (hm : IsL2Model ↥Kb) (hIV3 : IV3SylowLeaf x Kb)
    (h13 : Sec13.Prop12_1_nonE8)
    (hnonab : ∀ S : Subgroup G, IsSylow2In S ⊤ → ¬ (IsElemAb2 S ∧ Nat.card S = 8)) :
    ∃ (x' : G) (T V S : Subgroup G) (a b y : G), Sec13.Out13 G x' T V S a b y := by
  have : Kb.Normal := c.normal
  obtain ⟨S, U, hS, hU, hUn, hUC, F, _, _, e, N, hsit⟩ := exists_sit_L2 hIVK c hm
  have hk := kfacts_of_sit hIVK c hS hU hUn hUC hsit (ipTNormalLeaf_of_ivk hIVK x Kb)
  exact out13_of_kfacts Sec12.ig_15_3 Sec12.ig_16_2 Sec12.ig_15_15 h13 hk
    (iv3_of_nn hk.base (hIV3 c e N S hS hsit)) (hnonab S hS)

theorem out13_of_conf12B_A7 (hIVK : IVKA7Facts) {Kb : Subgroup (CentralizerBar x)}
    (c : Conf12B G x Kb) (hm : IsA7Model ↥Kb) (hIV3 : IV3SylowLeafA7 x Kb)
    (h13 : Sec13.Prop12_1_nonE8)
    (hnonab : ∀ S : Subgroup G, IsSylow2In S ⊤ → ¬ (IsElemAb2 S ∧ Nat.card S = 8)) :
    ∃ (x' : G) (T V S : Subgroup G) (a b y : G), Sec13.Out13 G x' T V S a b y := by
  have : Kb.Normal := c.normal
  have hx2 : x * x = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (by rw [c.x_order])
  have hx1 : x ≠ 1 := fun h => by
    have := c.x_order
    rw [h, orderOf_one] at this
    omega
  obtain ⟨S, hS, hxS, hTsyl, U, hU, hUn, hUC⟩ :=
    exists_setup c.simple c.nonabelian hx2 hx1 (exists_elemAb_eight x c.rankC)
  have hk := kfacts_A7 hIVK c hm hS hU hUn hUC hTsyl
  exact out13_of_kfacts Sec12.ig_15_3 Sec12.ig_16_2 Sec12.ig_15_15 h13 hk
    (iv3_of_nn hk.base (hIV3 c hm S hS hTsyl)) (hnonab S hS)

theorem out13_of_std_L2 (hIVK : IVKL2Facts) (hStd : Stage12.Std G) (h3 : pRank 2 G = 3)
    (hx : orderOf x = 2) {Kb : Subgroup (CentralizerBar x)} (hc : IsComponent Kb)
    (hm : HasL2Model ↥Kb (fun q => Odd q ∧ 3 < q))
    (hIV3 : IV3SylowLeaf x Kb) (h13 : Sec13.Prop12_1_nonE8) :
    ∃ (x' : G) (T V S : Subgroup G) (a b y : G), Sec13.Out13 G x' T V S a b y := by
  have hle : pRank 2 ↥(Cx x) ≤ 3 := (pRank_Cx_le x).trans h3.le
  have hnorm : Kb.Normal := normal_of_hasL2Model hle hc hm
  have hm' : IsL2Model ↥Kb := isL2Model_of_hasL2Model hm
  obtain ⟨hx1, hx2⟩ := orderOf_two_aux hx
  have h3C : 3 ≤ pRank 2 ↥(Cx x) := three_le_pRank_C hIVK.gen hIVK.h12c hx2 hx1 hm'
  have c : Conf12B G x Kb :=
    ⟨hStd.kps.1, hStd.kps.2.1, hx, hc, hnorm, le_antisymm hle h3C⟩
  exact out13_of_conf12B_L2 hIVK c hm' hIV3 h13 (hnonab_of_std hStd)

theorem out13_of_std_A7 (hIVK : IVKA7Facts) (hStd : Stage12.Std G) (h3 : pRank 2 G = 3)
    (hx : orderOf x = 2) {Kb : Subgroup (CentralizerBar x)} (hc : IsComponent Kb)
    (hm : IsA7Model ↥Kb)
    (hIV3 : IV3SylowLeafA7 x Kb) (h13 : Sec13.Prop12_1_nonE8) :
    ∃ (x' : G) (T V S : Subgroup G) (a b y : G), Sec13.Out13 G x' T V S a b y := by
  have hle : pRank 2 ↥(Cx x) ≤ 3 := (pRank_Cx_le x).trans h3.le
  have hnorm : Kb.Normal := normal_of_isA7Model hle hc hm
  obtain ⟨hx1, hx2⟩ := orderOf_two_aux hx
  have h3C : 3 ≤ pRank 2 ↥(Cx x) := three_le_pRank_C_A7 hIVK hx2 hx1 hm
  have c : Conf12B G x Kb := ⟨hStd.kps.1, hStd.kps.2.1, hx, hc, hnorm, le_antisymm hle h3C⟩
  exact out13_of_conf12B_A7 hIVK c hm hIV3 h13 (hnonab_of_std hStd)

theorem s_stage1_out13_Std_of_ext
    (hIV3 : ∀ (G : Type) [Group G] [Finite G], Stage12.Std G → pRank 2 G = 3 →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeaf x Kb)
    (hIV3A7 : ∀ (G : Type) [Group G] [Finite G], Stage12.Std G → pRank 2 G = 3 →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeafA7 x Kb) :
    ∀ (G : Type) [Group G] [Finite G], Stage12.Std G → pRank 2 G = 3 →
      L2Meets G (fun K _ => Nonempty (K ≃* alternatingGroup (Fin 7)) ∨
        HasL2Model K (fun q => Odd q ∧ 3 < q)) →
      ∃ (x : G) (T V S : Subgroup G) (a b y : G), Sec13.Out13 G x T V S a b y := by
  intro G _ _ hStd h3 ⟨x, hx, Kb, hc, hK⟩
  have h13 : Sec13.Prop12_1_nonE8 :=
    Sec13.prop12_1_nonE8_of_facts Bg.TwoGroups.Bridge13.sec13_ig_9_16
      Bg.TwoGroups.Bridge13.sec13_ig_10_31 Sec13.ig_15_15_sec13 Bg.ig_16_20
      Bg.TwoGroups.Bridge13.sec13_iv2_2_18 Bg.TwoGroups.Bridge13.sec13_iv2_2_7
  rcases hK with hA | hL
  · exact out13_of_std_A7 (ivkA7Facts_of_proved IVK.ivk_1_1f) hStd h3 hx hc hA
      (hIV3A7 G hStd h3 x Kb) h13
  · exact out13_of_std_L2 (ivkL2Facts_of_proved IVK.ivk_1_2_general IVK.ivk_1_3f_c) hStd h3 hx hc hL
      (hIV3 G hStd h3 x Kb) h13

end CFSG.GH74.GLS.Stage1.Thm6
