module

public import CFSG.Quasithin.EmptyFaithful.SzMSC3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S151TCHat
public import CFSG.GH74.QTGen4.DCopy.Quasithin.MS93.ASC134

public section

namespace CFSG.Quasithin.S151TC

section Case

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.S151TB

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem c134_exists_case_corr_F4 (hMS : MS93.AS_C_1_34_corr_F4) {L R H : Subgroup G} (hL : L ∈ cComp H)
    (hRN : R ≤ Subgroup.normalizer (L : Set G)) (hms : IsMSPair (L ⊔ R) R)
    (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) (hα : IsModO2Surj L α) :
    ∃ i : ℕ, MS93.IsC134CaseCorr i (L ⊔ R) R L :=
  hMS G (L ⊔ R) R L hms (mem_cComp_sup_of_normalizer hL hRN)
    (Subgroup.coe_mul_of_right_le_normalizer_left L R hRN)
    ⟨1, ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩

end Case

section Block

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.Quasithin.S151TB

theorem input15120L3Block_of_res_corr_F4 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hMS : MS93.AS_C_1_34_corr_F4) (hres : L3ResCorr) : S151TB.Input15120L3Block_F4 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hL3
  have hq : CFSG.IsQuasisimple (LStar L) := hc.hL.quasi
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hcomp
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hcomp
  have hRN : q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) := by
    have hqf := hc.ctx.qtfe
    rcases lemma_1_2_1_three hqf.qtke hqf.simple hqf.nonabelian h37 h38
        (hc.ctx.setting.pCore_g1_ne_bot hqf hc.ctx.mf) hcomp with hn | ⟨hn2, -⟩
    · exact (q1_1516_le Mc Z₁).trans ((mZ1516_le_g1 Mc Z₁).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn))
    · by_cases hn : (L.subgroupOf (g1_1516 Z₁)).Normal
      · exact (q1_1516_le Mc Z₁).trans ((mZ1516_le_g1 Mc Z₁).trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn))
      · exact q1_le_normalizer_of_nonnormal h37 hC129 hc hchar hcomp hL3 hn2
  have hcard : Nat.card (LStar L) = 168 := card_lStar_of_psl32 hq hL3
  obtain ⟨α, hαs, hαk⟩ := exists_epi_sl3_two hq hL3
  have hg : C27CaseG L (q1_1516 Mc Z₁) (mZ1516 Mc Z₁) :=
    c27_g_of_card168_F4 (hC27 G) hc.h18.five.2.2 hcomp hq hchar hc.hL.not_le hRN hcard
  obtain ⟨i, hi⟩ := c134_exists_case_corr_F4 hMS hcomp hRN hg.2.2 α ⟨hαs, hαk⟩
  match i, hi with
  | 1, hi => exact isLnBlock_three_of_isSL3Block hi.1 hcard
  | 2, hi => exact (hres.noCase2 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hL3 hRN hg hi).elim
  | 3, hi => exact (hres.noCase3 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hL3 hRN hg hi).elim
  | 4, hi => exact (hres.noCase4 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hL3 hRN hg hi).elim
  | 5, hi => exact isLnBlock_three_of_case5 hperf hchar hq hRN (commutator_ne_bot_of_caseG hg) hi.1
  | 0, hi => exact hi.elim
  | n + 6, hi => exact hi.elim

theorem input15120TwoBRes_of_res_corr_F4
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) (hMS : MS93.AS_C_1_34_corr_F4)
    (hres : L3ResCorr) : S151TB.Input15120TwoBRes_F4 :=
  ⟨input15120NoHatA6_holds_F4 h37 h38 hC27, input15120L3Block_of_res_corr_F4 h37 h38 hC27 hC129 hMS hres⟩

theorem input15120TwoB_of_l3res_corr_F4
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) (hMS : MS93.AS_C_1_34_corr_F4)
    (hres : L3ResCorr) : Input15120TwoB_F4 :=
  S151TB.input15120TwoB_of_res_F4 h37 h38 hC27
    (input15120TwoBRes_of_res_corr_F4 h37 h38 hC27 hC129 hMS hres)

end Block

end CFSG.Quasithin.S151TC

