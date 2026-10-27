module

public import CFSG.GH74.QTGen4.Ch12.DIGen4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma4FiveFinal
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma4

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open CFSG.Blueprint

theorem isHzOne_normalizer_F4 {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    IsHzOne T L V₁ (Subgroup.normalizer (V₁ : Set G)) := by
  have hlOne : lOne L V₁ ≤ L ⊓ Subgroup.normalizer (V₁ : Set G) := oTwoUpper_le _
  refine ⟨⟨sup_le (hlOne.trans inf_le_right) hV₁.2.2, fun hb => ?_⟩, le_rfl,
    lemma12_8_3_four_F4 h12213 h hV₁⟩
  have h1 := CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 V₁ (IsPGroup.of_card hV₁.2.1)
  rw [hb, le_bot_iff] at h1
  have h2 := hV₁.2.1
  rw [h1, Subgroup.card_bot] at h2
  norm_num at h2

theorem case1294FiveFinal_F4_of
    (h1222 : CFSG.Quasithin.H13.Stmt12_2_2_F4)
    (h12213 : CFSG.Quasithin.H13.Stmt12_2_13_F4) :
    CFSG.Quasithin.H13.Case1294FiveFinal_F4 := by
  intro G _ _ T L V _ V₁ V₂ K₁ hs _ _ _ D hD5
  exfalso
  have hUT : u128 V V₁ ≤ T :=
    (lemma12_8_4_one_F4 h1222 hs.hyp hs.v1 (isHzOne_normalizer_F4 h12213 hs.hyp hs.v1)).G22_three.1
  have hG : CFSG.GH74.Gen4 G := CFSG.GH74.QTGen4.Finite4.gen4
  have hU2 : IsPGroup 2 ↥(u128 V V₁) := hs.hyp.hyp.sylow.1.to_le hUT
  have h4 := hatModel_finrank_le hG hU2 D
  have h6 := hD5.1
  omega

end CFSG.GH74.QTGen4.Leaves
