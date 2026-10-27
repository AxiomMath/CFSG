module

public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma8
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4E61

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

@[expose] def CharTwo1248_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Cx1242 G T L V →
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
      ∀ U : Subgroup G, U ≤ V → U.relIndex V = 2 →
        ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) →
          QuasithinUnique.CharTwo (Subgroup.centralizer (U : Set G))

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

theorem lemma12_4_8_of_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) (hpre : Pre1242_F4)
    (h3228 : Stmt3_2_2_eight) (h614 : ASInputs.AS_E_6_14) (hL3 : L3HyperplaneFact1248)
    (hG2 : G2HyperplaneFact1248) (hchar : CharTwo1248_F4) : Lemma12_4_8_F4 := by
  intro G _ _ T L V hcx hq
  have hyp := hcx.hyp
  obtain ⟨z, hf⟩ := CxFacts.of_F4 h331 h1222 hpre hcx hq
  have := hf.comm
  have hW2 : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hf.sq w w.2)
  have hV2 : IsPGroup 2 ↥V := hyp.sylow.1.to_le hf.le_T
  have hzV : z ∈ V := hf.mem_zV.1
  have hV1 : V ≠ ⊥ := fun h => hf.ne_one (by rw [h] at hzV; exact Subgroup.mem_bot.1 hzV)
  have hE := hypE61_of_cx_F4 h331 h1222 h323 h3228 hcx hf.isElemAbelian hV1 hf.le_T hf.T_le
    hf.normalizes
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hf.normalizes hf.T_le

  have hcommV := commV_autOn_eq_top hf.normalizes hf.commutator
  have hfix : Nat.card (fixV (autOn L V)) = 2 := by
    rw [fixV_autOn_eq hf.normalizes, card_subgroupOf_eq_card_inf, hf.card_zV]
  have hLX : autOn L V ≤ autOn (L ⊔ T) V := A4.autOn_mono le_sup_left
  have hXN : autOn (L ⊔ T) V ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
    autOn_le_normalizer_autOn_of_le (sup_le Subgroup.le_normalizer hyp.normalizes)
  have hX2 : ∀ y ∈ autOn (L ⊔ T) V, ∃ e : ℕ, y ^ 2 ^ e ∈ autOn L V :=
    InternalSec.autOn_two_of hf.normalizes fun y hy => by
      obtain ⟨k, hk⟩ := E6.exists_pow_mem_of_mem_sup hyp.sylow.1 hyp.normalizes hy
      exact ⟨k, le_sup_left (b := Subgroup.centralizer (V : Set G)) hk⟩

  have hker : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) := by
    have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rcases hq with h3 | hU
      · obtain ⟨e⟩ := h3
        have := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
        exact e.isSimpleGroup
      · exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel hU
    obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_quotient hf.normalizes hf.pCore hs hf.notCent
    have hsA : IsSimpleGroup ↥(autOn L V) := eA.isSimpleGroup
    have hO2 : pCoreOf 2 (autOn L V) = ⊥ := by
      refine pCoreOf_eq_bot_of_simple hsA fun hp => ?_
      obtain ⟨n, hn⟩ := hp.exists_card_eq
      rw [Nat.card_congr eA.toEquiv] at hn
      rcases hq with h3 | hU
      · rw [card_quot_of_sl_three h3] at hn
        have h8 : n < 8 :=
          (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 (by rw [← hn]; norm_num)
        interval_cases n <;> norm_num at hn
      · rw [card_of_lieModel_psu_three_three hU] at hn
        have h13 : n < 13 :=
          (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 (by rw [← hn]; norm_num)
        interval_cases n <;> norm_num at hn
    exact InternalSec.isPGroup_ker_of_simple hf.normalizes hs hO2 hf.notCent

  have key : ∀ U : Subgroup G, U ≤ V → U.relIndex V = 2 →
      Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    intro U hUV hidx
    by_contra hUC
    by_cases hzU : z ∈ U
    · apply hUC
      rw [← hf.MN, hf.MC]
      exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzU)
    have hidx' : (U.subgroupOf V).index = 2 := hidx
    have hU1 : U ≠ ⊥ := by
      rintro rfl

      rw [Subgroup.relIndex_bot_left] at hidx
      have hVZ : V ⊓ Subgroup.centralizer (L : Set G) = V :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [hf.card_zV, hidx]))
      apply hf.notCent
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      rw [← hVZ] at hv
      exact (Subgroup.mem_centralizer_iff.1 hv.2 l hl).symm

    have hMU : Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) ≤
        Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) := by
      rintro m ⟨hmM, hmU⟩
      refine ⟨hmM, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
      have hmz : m * z = z * m := by
        rw [hf.MC] at hmM
        exact Subgroup.mem_centralizer_singleton_iff.1 hmM
      by_cases hvU : v ∈ U
      · exact Subgroup.mem_centralizer_iff.1 hmU v hvU
      have hzu : z⁻¹ * v ∈ U := by
        have hz' : (⟨z, hzV⟩ : ↥V)⁻¹ ∉ U.subgroupOf V := fun h =>
          hzU (by simpa using Subgroup.mem_subgroupOf.1 h)
        have hv' : (⟨v, hv⟩ : ↥V) ∉ U.subgroupOf V := fun h => hvU (Subgroup.mem_subgroupOf.1 h)
        exact Subgroup.mem_subgroupOf.1
          ((Subgroup.mul_mem_iff_of_index_two hidx').2 (iff_of_false hz' hv'))
      have hcu := Subgroup.mem_centralizer_iff.1 hmU _ hzu
      calc v * m = z * ((z⁻¹ * v) * m) := by group
        _ = z * (m * (z⁻¹ * v)) := by rw [hcu]
        _ = (z * m) * (z⁻¹ * v) := by group
        _ = (m * z) * (z⁻¹ * v) := by rw [hmz]
        _ = m * v := by group
    have hres := (twoPrimeResidual_le_self _).trans hMU
    have hcharU := hchar G T L V hcx hq U hUV hidx hUC
    have hnotle : ¬ fixV (autOn L V) ≤ U.subgroupOf V := by
      intro h
      apply hzU
      have h1 : (⟨z, hzV⟩ : ↥V) ∈ fixV (autOn L V) := by
        rw [fixV_autOn_eq hf.normalizes]
        exact hf.mem_zV.2
      exact Subgroup.mem_subgroupOf.1 (h h1)

    obtain ⟨hmaxb, hidxb, Y, hYL, hY3, hYC⟩ : IsMaxSubgroupIn (autOn (L ⊔ T) V)
        (autOn (L ⊔ T) V ⊓ stabSub (U.subgroupOf V)) ∧
        (autOn (L ⊔ T) V ⊓ stabSub (U.subgroupOf V)).relIndex (autOn (L ⊔ T) V) ≠ 2 ∧
        ∃ Y : Subgroup (MulAut ↥V), Y ≤ autOn L V ⊓ stabSub (U.subgroupOf V) ∧
          Nat.card Y = 3 ∧ ¬ Y ≤ centSub (U.subgroupOf V) := by
      rcases hq with h3 | hU
      · obtain ⟨hV16, hGrs, hGr, hnat⟩ := cx_l3_module_F4 h1222 hcx hf h3
        obtain ⟨-, hTeq⟩ := cx_autOn_T_eq hcx hf hnat
        have hX : autOn (L ⊔ T) V = autOn L V := by
          refine le_antisymm ?_ hLX
          unfold autOn
          rw [Subgroup.subgroupOf_sup hf.normalizes hf.T_le, Subgroup.map_sup]
          refine sup_le le_rfl ?_
          have h1 : autOn T V ≤ autOn L V := by
            rw [hTeq]
            exact A4.autOn_mono inf_le_right
          exact h1
        rw [hX]
        exact hL3 ↥V hW2 hV16 (autOn L V) hGrs hGr hcommV hfix (U.subgroupOf V) hidx' hnotle
      · obtain ⟨_, hcases⟩ := modules_cases_of_hyp1223_F4 h1222 hyp
        have hnat : G2NaturalDerived (autOn L V) ⊤ (fixV (autOn L V)) 1 := by
          rw [fixV_autOn_eq hf.normalizes]
          exact hcases.2.1 hU
        exact hG2 ↥V hW2 (autOn (L ⊔ T) V) (autOn L V) hLX hXN hX2 hcommV hfix hnat
          (U.subgroupOf V) hidx' hnotle

    have hmax := isMaxSubgroupIn_of_autOn hUV hLTV hmaxb
    have hidx2 : ((L ⊔ T) ⊓ Subgroup.normalizer (U : Set G)).relIndex (L ⊔ T) ≠ 2 := by
      rw [relIndex_inf_normalizer_eq hUV hLTV]
      exact hidxb
    have hY := exists_card_three_of_autOn hUV hker hYL hY3 hYC
    have hCM := h614 G T (Subgroup.normalizer (L : Set G)) V U (L ⊔ T) hE hU1 hUV hres hcharU
      (Or.inr hY) le_sup_right (sup_le_normalizer_of_cx_F4 h1222 h3228 hcx)
      (isUniqueM_sup_of_cx_F4 h331 hcx) hmax hidx2
    exact hUC (hCM.trans hf.MN.le)

  have h2 : (2 : ℕ∞) ≤ E3.rParam V := by
    unfold E3.rParam
    refine le_iInf₂ fun U hU => ?_
    obtain ⟨hUV, hUC⟩ := hU
    by_contra hlt
    have hk : E3.mQuot V U ≤ 1 := by
      push Not at hlt
      have : E3.mQuot V U < 2 := by exact_mod_cast hlt
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with h0 | h1
    · exact hUC (((E3.mQuot_eq_zero_iff hV2 hUV).mp h0) ▸ Subgroup.centralizer_le_normalizer _)
    · exact hUC (key U hUV (by rw [E3.relIndex_eq_two_pow hV2, h1, pow_one]))
  exact lt_of_lt_of_le (by norm_num) h2

end CFSG.Quasithin.H13
