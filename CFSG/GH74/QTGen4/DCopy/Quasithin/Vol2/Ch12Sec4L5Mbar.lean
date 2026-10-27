module

public import CFSG.Quasithin.Vol2.Ch12Sec4L5Mbar
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4E61
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4L5Cx

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {z : G}

namespace Cx5Facts

theorem exists_offender_F4 [IsMulCommutative ↥V] (h1229 : Stmt12_2_9_F4) (hpre : Pre1242_F4)
    (hcx : Cx1242 G T L V) (hf : Cx5Facts G T L V z) :
    ∃ A : Subgroup (MulAut ↥V), IsFFStarOffender (autOn (L ⊔ T) V) A := by
  have hJ : L = ⁅L, thompsonJ T⁆ :=
    lemma12_4_3_two_of_F4 h1229 (lemma12_4_3_one_of_pre_F4 hpre) G T L V hcx
  have hW2 : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hf.sq w w.2)
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
  have hBX : autOn B V ≤ autOn (L ⊔ T) V := autOn_mono (hBT.trans le_sup_right)
  have hB1 : autOn B V ≠ ⊥ := by
    intro h
    apply hBV
    intro b hb
    have h1 : conjAct V ⟨b, hBN hb⟩ ∈ autOn B V :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hb)
    rw [h, Subgroup.mem_bot] at h1
    exact A4.conjAct_eq_one_iff.1 h1
  have hA2 : IsA2 (autOn (L ⊔ T) V) (autOn B V) := ⟨hBX, hB1, isElemAbelian2_autOn' hB.2.1⟩
  have hr : Nat.card ↥V ≤ Nat.card (autOn B V) * Nat.card (fixV (autOn B V)) := by
    have h1 := card_le_relIndex_mul_card hf.isElemAbelian hf.le_T hB
    rwa [← card_autOn_eq_relIndex hBN, ← card_subgroupOf_eq_card_inf,
      ← fixV_autOn_eq hBN] at h1
  obtain ⟨A, -, hA, -⟩ := B1_4_4_le hW2 hA2 ((rAV_le_one_iff hW2 hA2).2 hr)
  exact ⟨A, hA⟩

theorem mbar_eq_F4 (h1222 : Stmt12_2_2_F4) (h3228 : Stmt3_2_2_eight) (h12210 : Stmt12_2_10_F4)
    (h1229 : Stmt12_2_9_F4) (hpre : Pre1242_F4) (h42 : AsB42) (hcx : Cx1242 G T L V)
    (hf : Cx5Facts G T L V z)
    (h5 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) :
    autOn (L ⊔ T) V = autOn L V := by
  have := hf.comm
  have hW2 : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hf.sq w w.2)
  obtain ⟨A, hA⟩ := hf.exists_offender_F4 h1229 hpre hcx
  have hc := h42 ↥V hW2 (autOn (L ⊔ T) V) (autOn L V) (hf.b4Hyp_F4 h1222 h3228 h12210 hcx h5) A hA
  obtain ⟨hXJ, hJL, -⟩ := b42Case11_of_card hf.card (hf.card_lbar h5) hc
  exact hXJ.trans hJL

theorem mbarV_eq_F4 (h1222 : Stmt12_2_2_F4) (h3228 : Stmt3_2_2_eight) (h12210 : Stmt12_2_10_F4)
    (h1229 : Stmt12_2_9_F4) (hpre : Pre1242_F4) (h42 : AsB42) (hcx : Cx1242 G T L V)
    (hf : Cx5Facts G T L V z)
    (h5 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) :
    autOn (Subgroup.normalizer (L : Set G)) V = autOn L V := by
  have h1 : autOn (Subgroup.normalizer (L : Set G)) V = hcx.hyp.MVbar := by
    show autOn (Subgroup.normalizer (L : Set G)) V =
      autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V
    unfold autOn
    rw [Subgroup.inf_subgroupOf_right]
  rw [h1, (h12210 G T L V hcx.hyp).2.2, ← hf.autOn_sup,
    hf.mbar_eq_F4 h1222 h3228 h12210 h1229 hpre h42 hcx h5]

theorem three_le_mParam_F4
    (h1222 : Stmt12_2_2_F4) (h3228 : Stmt3_2_2_eight) (h12210 : Stmt12_2_10_F4)
    (h1229 : Stmt12_2_9_F4) (hpre : Pre1242_F4) (h42 : AsB42) (hcx : Cx1242 G T L V)
    (hf : Cx5Facts G T L V z)
    (h5 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) :
    3 ≤ E3.mParam (autI hf.isElemAbelian (Subgroup.normalizer (L : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

  have hMV : autI hf.isElemAbelian (Subgroup.normalizer (L : Set G)) =
      autI hf.isElemAbelian L := hf.mbarV_eq_F4 h1222 h3228 h12210 h1229 hpre h42 hcx h5
  have hcardL : Nat.card ↥(autI hf.isElemAbelian L) = 9999360 := hf.card_lbar h5
  obtain ⟨φ⟩ : Nonempty (↥(autI hf.isElemAbelian L) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := hf.lbar_equiv h5
  have hirr : ∀ W : Subgroup (IntMod V hf.isElemAbelian),
      (∀ a ∈ autI hf.isElemAbelian L, ∀ w ∈ W, (a : MulAut (IntMod V hf.isElemAbelian)) w ∈ W) →
        W = ⊥ ∨ W = ⊤ := hf.irr_lbar
  have hcard : Nat.card (IntMod V hf.isElemAbelian) = 2 ^ 10 := hf.card
  have hev : Even (Nat.card ↥(autI hf.isElemAbelian L)) := by
    rw [hcardL]
    exact ⟨4999680, by norm_num⟩
  unfold E3.mParam
  rw [hMV, ite_eq_left hev]
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(autI hf.isElemAbelian L)) 2
    (even_iff_two_dvd.1 hev)
  refine le_csInf ⟨_, (t : MulAut (IntMod V hf.isElemAbelian)), t.2,
    by rw [Subgroup.orderOf_coe, ht], rfl⟩ ?_
  rintro _ ⟨s, hs, hso, rfl⟩
  have hs1 : s ≠ 1 := fun h => by
    rw [h, orderOf_one] at hso
    norm_num at hso
  have hs2 : s * s = 1 := by rw [← pow_two, ← hso, pow_orderOf_eq_one]
  exact three_le_rkIdx hcard
    (card_fixV_le_of_sl5 (fun v => IntMod.sq_eq_one v) hcard φ hirr hs hs1 hs2)

theorem hypE61_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (hcx : Cx1242 G T L V) (hf : Cx5Facts G T L V z) :
    E6.HypE61 T (Subgroup.normalizer (L : Set G)) V :=
  hypE61_of_cx_F4 h331 h1222 h323 h3228 hcx hf.isElemAbelian hf.ne_bot hf.le_T hf.T_le hf.normalizes

theorem one_lt_sParam_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (h12210 : Stmt12_2_10_F4) (h1229 : Stmt12_2_9_F4) (hpre : Pre1242_F4)
    (h42 : AsB42) (h63 : ASInputs.AS_E_6_3) (hcx : Cx1242 G T L V) (hf : Cx5Facts G T L V z)
    (h5 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) :
    1 < E3.sParam hf.isElemAbelian := by
  have hm := hf.three_le_mParam_F4 h1222 h3228 h12210 h1229 hpre h42 hcx h5
  obtain ⟨-, hs⟩ := h63 G T (Subgroup.normalizer (L : Set G)) V hf.isElemAbelian
    (hf.hypE61_F4 h331 h1222 h323 h3228 hcx) (by omega)
  rw [hs]
  omega

end Cx5Facts

end CFSG.Quasithin.H13
