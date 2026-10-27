module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8Fin
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4C8Stmt

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S1248
open scoped IsMulCommutative

namespace S1248

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

section

theorem sixteen_le_card_V_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (hpre : Pre1242_F4) {T L V : Subgroup G}
    (hcx : Cx1242 G T L V)
    (hq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) : 16 ≤ Nat.card V := by
  obtain ⟨z, hf⟩ := CxFacts.of_F4 h331 h1222 hpre hcx hq
  have := hf.comm
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hf.normalizes
  have hVp : IsPGroup 2 V := hcx.hyp.sylow.1.to_le hf.le_T
  have hZ2 : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
    rw [hf.zV, Nat.card_zpowers, hf.order]
  obtain ⟨hs, h24⟩ : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      24 < Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases hq with hL3 | hU
    · obtain ⟨e⟩ := hL3
      have := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
      refine ⟨e.isSimpleGroup, ?_⟩
      rw [card_quot_of_sl_three ⟨e⟩]
      norm_num
    · refine ⟨CFSG.Timmesfeld.isSimpleGroup_of_lieModel hU, ?_⟩
      rw [card_of_lieModel_psu_three_three hU]
      norm_num
  have h4 := four_lt_relIndex_of_simple hLV hf.commutator hf.notCent hf.pCore hs h24
  have h1 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (L : Set G)) V
  rw [inf_eq_left.2 (inf_le_left : V ⊓ Subgroup.centralizer (L : Set G) ≤ V), hZ2] at h1
  have h8 : 8 < Nat.card V := by omega
  obtain ⟨n, hn⟩ := hVp.exists_card_eq
  rw [hn] at h8 ⊢
  by_contra h
  push Not at h
  have hn3 : n ≤ 3 := by
    by_contra h'
    push Not at h'
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h'
    omega
  interval_cases n <;> norm_num at h8

end

end S1248

section

theorem oddFinal1248_of_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (hpre : Pre1242_F4) : OddFinal1248_F4 := by
  intro G _ _ T L V U hS P _ hPodd _ hMP
  classical
  obtain ⟨z, hf⟩ := CxFacts.of_F4 h331 h1222 hpre hS.cx hS.quot
  have hyp := hS.cx.hyp
  have hev : CFSG.Open.evenRank G ≤ 2 := hyp.qtke.2.2
  have h16 := S1248.sixteen_le_card_V_F4 h331 h1222 hpre hS.cx hS.quot
  have hVp : IsPGroup 2 V := hyp.sylow.1.to_le hf.le_T
  have hVel : IsElemAbelian 2 V := ⟨hf.comm, hf.sq⟩
  have hLp : ⁅L, L⁆ = L := hyp.maximal.1.2.1.2.1
  have hVM : V ≤ Subgroup.normalizer (L : Set G) := by
    rw [hf.MN]
    exact Subgroup.le_normalizer
  have hVH : V ≤ Subgroup.normalizer (P : Set G) := hVM.trans hMP
  have hLH : L ≤ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer.trans hMP
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p (pCoreOf p (Subgroup.normalizer (P : Set G))) ≤ 2 := by
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    exact S1248.pRank_le_two_of_normalized hev hp hp2
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup p _) hVel h16
      (hVH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p _))
  have hcent := a126_one hLH (C2Nine.opResidual_eq_of_perfect hLp) hVH hVp hf.commutator hrank
    (C2Nine.frattiniIn_eq_bot_of_isElemAbelian hVel)
  have hPO : P ≤ fusionOddCoreOf (Subgroup.normalizer (P : Set G)) :=
    E6.le_oddCoreIn_of_odd Subgroup.le_normalizer le_rfl hPodd
  exact hcent.trans (Subgroup.centralizer_le hPO)

end

end CFSG.Quasithin.H13
