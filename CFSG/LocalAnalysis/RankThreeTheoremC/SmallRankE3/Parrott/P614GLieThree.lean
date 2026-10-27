module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GLie
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614R3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GSylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {M B H S K : Subgroup G} {z : G}

theorem pRank_top_eq_one (c : Ctx M B H S K z) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Kbar K)) = 1 := by
  refine le_antisymm c.pRank_top_le ?_
  have hz3 : c.zbar ^ 3 = 1 := by
    have h := pow_orderOf_eq_one c.zbar
    rwa [c.orderOf_zbar] at h
  have hE : IsElemAbelian 3 (zpowers c.zbar) := by
    refine ⟨IsMulCommutative.of_setLike_mul_comm fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE
    (by rw [Nat.card_zpowers, c.orderOf_zbar, pow_one])

theorem exists_par_sylow_three (c : Ctx M B H S K z) (h135 : KFact135Three)
    (hR : pCoreOf 2 H < kRad H S K) :
    ∃ T : Subgroup G, T ≤ kPar H S K ∧ IsPGroup 2 T ∧
      ¬ 2 ∣ (T.subgroupOf (K ⊔ pCoreOf 2 H)).index := by
  have := c.isSimpleGroup
  obtain ⟨Tb, hTN, hT2, hTi⟩ := h135 (Kbar K) c.isSimpleGroup c.exists_ne_comm c.isChevTwo
    c.pRank_top_eq_one (rbar K S) c.isPGroup_rbar (c.rbar_ne_bot hR) c.pCoreOf_normalizer_rbar
  refine ⟨pre K Tb ⊔ pCoreOf 2 H, le_inf (sup_le_sup_right (pre_le K Tb) _) ?_,
    c.isPGroup_pre_sup hT2, by rwa [c.index_pre_sup]⟩
  refine sup_le (fun t ht => ?_) (fun o ho => le_normalizer (c.kRad_eq ▸ mem_sup_right ho))
  have htK := pre_le K Tb ht
  have hnorm := hTN ((mem_pre htK).1 ht)
  rw [c.kRad_eq]
  refine inf_normalizer_le_normalizer_sup _ _
    ⟨?_, c.H_le_normalizer_core (c.K_le htK)⟩
  show t ∈ normalizer ((pre K (rbar K S) : Subgroup G) : Set G)
  rw [mem_normalizer_iff]
  intro g
  have hrho : ∀ u ∈ rbar K S, c.rho ⟨t, c.K_le htK⟩ u ∈ rbar K S := fun u hu => by
    rw [c.rho_of_mem_K htK, MulAut.conj_apply]
    exact (mem_normalizer_iff.mp hnorm u).1 hu
  have hrho' : ∀ u ∈ rbar K S, c.rho ⟨t⁻¹, H.inv_mem (c.K_le htK)⟩ u ∈ rbar K S := fun u hu => by
    rw [c.rho_of_mem_K (K.inv_mem htK), MulAut.conj_apply]
    have : (QuotientGroup.mk ⟨t⁻¹, K.inv_mem htK⟩ : Kbar K) =
        (QuotientGroup.mk ⟨t, htK⟩)⁻¹ := rfl
    rw [this]
    have := (mem_normalizer_iff.mp (inv_mem hnorm) u).1 hu
    simpa using this
  refine ⟨fun hg => c.conj_mem_pre (c.K_le htK) hrho hg, fun hg => ?_⟩
  have := c.conj_mem_pre (H.inv_mem (c.K_le htK)) hrho' hg
  simpa [mul_assoc] using this

theorem lieCase_three {x : G} (c : Ctx M (zpowers x ⊔ zpowers z) H S K z) (hTI : KFactBenderTI)
    (hGen : KFactBenderGen) (hCGT : CFSG.AGLEmbedding.AschbacherLocalCGTBlock)
    (h135 : KFact135Three) (hR : pCoreOf 2 H < kRad H S K) : LieCase M H S K x z where
  chev := c.isChevTwo
  not_bender := fun h => c.false_of_bender hTI hGen hR h
  rad_gt := hR
  rad_not_sylow := by
    by_contra h
    exact c.false_of_sylow hTI hGen hCGT hR h
  par_core := c.pCoreOf_kPar
  par_sylow := c.exists_par_sylow_three h135 hR
  par_mem := zpowers_le.mpr ⟨mem_sup_left c.z_mem_K, c.le_normalizer_kRad c.z_mem_H
    (c.B_le_normalizer_S c.z_mem_B)⟩
  par_inv := sup_le (fun _ hs => c.le_normalizer_kPar (c.S_le hs) (le_normalizer hs))
    (fun _ hb => c.le_normalizer_kPar (c.B_le hb) (c.B_le_normalizer_S hb))
  par_le := inf_le_right.trans (c.normalizer_kRad_le hR)

end Ctx

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G
