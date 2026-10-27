module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8X
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4C8Fin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

namespace S1248

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {L V U : Subgroup G}
  [IsMulCommutative ↥V]

variable {T : Subgroup G} {z : G}

theorem exists_offender_autOn_T_F4 (h1229 : Stmt12_2_9_F4) (hpre : Pre1242_F4)
    (hcx : Cx1242 G T L V) (hf : CxFacts G T L V z) :
    ∃ B : Subgroup G, B ≤ T ∧ autOn B V ≠ ⊥ ∧ IsElemAbelian2 (autOn B V) ∧
      Nat.card ↥V ≤ Nat.card (autOn B V) * Nat.card (fixV (autOn B V)) := by
  have hJ : L = ⁅L, thompsonJ T⁆ :=
    lemma12_4_3_two_of_F4 h1229 (lemma12_4_3_one_of_pre_F4 hpre) G T L V hcx
  obtain ⟨B, hB, hBV⟩ : ∃ B : Subgroup G, IsMaxElemAbelian T B ∧
      ¬ B ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hall
    push Not at hall
    have hJV : thompsonJ T ≤ Subgroup.centralizer (V : Set G) := iSup₂_le fun B hB => hall B hB
    apply hf.notCent
    rw [hJ, Subgroup.commutator_le]
    intro l hl j hj
    have hjN : j ∈ Subgroup.normalizer (V : Set G) :=
      hf.T_le ((iSup₂_le fun B (hB : IsMaxElemAbelian T B) => hB.1 : thompsonJ T ≤ T) hj)
    have hj1 : conjAct V ⟨j, hjN⟩ = 1 := A4.conjAct_eq_one_iff.2 (hJV hj)
    have h1 : conjAct V ⁅(⟨l, hf.normalizes hl⟩ : Subgroup.normalizer (V : Set G)),
        ⟨j, hjN⟩⁆ = 1 := by
      rw [map_commutatorElement, hj1, commutatorElement_one_right]
    exact A4.conjAct_eq_one_iff.1 h1
  have hBT : B ≤ T := hB.1
  have hBN : B ≤ Subgroup.normalizer (V : Set G) := hBT.trans hf.T_le
  have hB1 : autOn B V ≠ ⊥ := by
    intro h
    apply hBV
    intro b hb
    have h1 : conjAct V ⟨b, hBN hb⟩ ∈ autOn B V :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hb)
    rw [h, Subgroup.mem_bot] at h1
    exact A4.conjAct_eq_one_iff.1 h1
  have hr : Nat.card ↥V ≤ Nat.card (autOn B V) * Nat.card (fixV (autOn B V)) := by
    have h1 := card_le_relIndex_mul_card hf.isElemAbelian hf.le_T hB
    rwa [← card_autOn_eq_relIndex hBN, ← card_subgroupOf_eq_card_inf,
      ← fixV_autOn_eq hBN] at h1
  exact ⟨B, hBT, hB1, isElemAbelian2_autOn' hB.2.1, hr⟩

theorem autOn_T_not_le_F4 (h1229 : Stmt12_2_9_F4) (hpre : Pre1242_F4)
    (hcx : Cx1242 G T L V) (hf : CxFacts G T L V z) (hoff : G2DerivedNoOffender1248)
    (hW : ∀ w : ↥V, w ^ 2 = 1) (hcomm : commV (autOn L V) = ⊤)
    (hfix : Nat.card (fixV (autOn L V)) = 2)
    (hnat : G2NaturalDerived (autOn L V) ⊤ (fixV (autOn L V)) 1) :
    ¬ autOn T V ≤ autOn L V := by
  intro hTL
  obtain ⟨B, hBT, hB1, hBe, hr⟩ := exists_offender_autOn_T_F4 h1229 hpre hcx hf
  exact hoff ↥V hW (autOn L V) hcomm hfix hnat (autOn B V) ((A4.autOn_mono hBT).trans hTL) hB1
    hBe hr

end S1248

open S1248

section

theorem hypX1248_of_outer_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h1229 : Stmt12_2_9_F4) (hpre : Pre1242_F4)
    (hoff : G2DerivedNoOffender1248) (hG2 : G2HypXFact1248) : HypX1248_F4 := by
  intro G _ _ T L V U hS
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hS.cx.hyp
  obtain ⟨z, hf⟩ := CxFacts.of_F4 h331 h1222 hpre hS.cx hS.quot
  obtain ⟨_, hcases⟩ := modules_cases_of_hyp1223_F4 h1222 hyp
  have := hf.comm
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hf.normalizes
  have hW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hf.sq w w.2)
  have hZ2 : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
    rw [hf.zV, Nat.card_zpowers, hf.order]
  have hcommGr : commV (autOn L V) = ⊤ := commV_autOn_eq_top hLV hf.commutator
  have hfixGr : Nat.card (fixV (autOn L V)) = 2 := by
    rw [fixV_autOn_eq hLV, card_subgroupOf_eq_card_inf, hZ2]
  have hU' : (U.subgroupOf V).index = 2 := hS.hyper
  have hzU : z ∉ U := by
    intro hzU
    apply hS.escape
    rw [← hf.MN, hf.MC]
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzU)
  have hnot : ¬ fixV (autOn L V) ≤ U.subgroupOf V := by
    intro h
    rw [fixV_autOn_eq hLV] at h
    have hz : (⟨z, hf.mem_zV.1⟩ : ↥V) ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V :=
      Subgroup.mem_subgroupOf.2 hf.mem_zV.2
    exact hzU (Subgroup.mem_subgroupOf.1 (h hz))
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases hS.quot with h3 | hU
    · obtain ⟨e⟩ := h3
      have := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
      exact e.isSimpleGroup
    · exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel hU
  have hker := isPGroup_ker_actHom hLV hf.pCore hs hf.notCent
  rcases hS.quot with h3 | hU
  ·
    obtain ⟨e⟩ := h3
    have h168 := card_quot_of_sl_three ⟨e⟩
    obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_quotient hLV hf.pCore hs hf.notCent
    have hGrs : IsSimpleGroup (autOn L V) := eA.isSimpleGroup
    have hGr : Nat.card (autOn L V) = 168 := by rw [Nat.card_congr eA.toEquiv, h168]
    have hV16 : Nat.card V = 2 ^ 4 :=
      le_antisymm (hcases.1 ⟨e⟩) (by
        have := sixteen_le_card_V_F4 h331 h1222 hpre hS.cx hS.quot
        norm_num
        exact this)
    obtain ⟨Y, hY, hY3, hYU, t, ht, htU, ht2⟩ :=
      L3Hyp.exists_hypX hW hV16 (autOn L V) hGrs hGr hcommGr hfixGr (U.subgroupOf V) hU' hnot
    left
    obtain ⟨X, hX, hX3, hXU, l, hl, hlU, hl2⟩ :=
      lift_hypX_one hLV hS.le hker hY hY3 hYU ht htU (by rw [ht2]; exact Subgroup.one_mem _)
    exact ⟨X, hX, hX3, hXU, l, ⟨hLV hl.1, hl.2⟩, hlU, hl2⟩
  ·
    have hnat : G2NaturalDerived (autOn L V) ⊤ (fixV (autOn L V)) 1 := by
      rw [fixV_autOn_eq hLV]
      exact hcases.2.1 hU
    have hTL : T ≤ Subgroup.normalizer (L : Set G) := by
      rw [hf.MN]
      exact hf.T_le
    have hLTL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
    have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hf.T_le
    have hlt : autOn L V < autOn (L ⊔ T) V := by
      refine lt_of_le_of_ne (A4.autOn_mono le_sup_left) fun heq => ?_
      refine autOn_T_not_le_F4 h1229 hpre hS.cx hf hoff hW hcommGr hfixGr hnat ?_
      rw [heq]
      exact A4.autOn_mono le_sup_right
    rcases hG2 ↥V hW (autOn L V) hcommGr hfixGr hnat (autOn (L ⊔ T) V) hlt
        (autOn_le_normalizer_autOn_of_le hLTL) (U.subgroupOf V) hU' hnot with
      ⟨Xb, hXb, hXb3, hXbU, t, ht, htU, ht2⟩ | ⟨Yb, hYb, hYb27, hYb3, hYbU⟩
    · left
      exact lift_hypX_one_of_normalizer hLV hS.le hker hLTL hLTV hXb hXb3 hXbU ht htU ht2
    · right
      exact lift_hypX_two hLV hS.le hker hYb hYb27 hYb3 hYbU

end

end CFSG.Quasithin.H13
