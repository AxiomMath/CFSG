module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOneFourCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K7145Comp
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.LocalAnalysis.RankThreeTheoremC (KFactOutCyclic)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open S15.K7145Proof (outerAction)

theorem sevenOneFourCover_of_outCyclic (h : KFactOutCyclic) : SevenOneFourCover := by
  intro X _ _ hK p hp hp2 L hL hLn hr S hS
  haveI := hLn
  haveI : Group.IsPerfect ↥L := hL.1.1
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  have hq : CFSG.Open.IsQuasisimple ↥L := ⟨Group.isPerfect_def.mp hL.1.1, hL.1.2.1⟩
  have hcyc : ∀ {Y : Type} [Group Y] [Finite Y] (P : Subgroup Y), IsPGroup p P →
      CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 1 → IsCyclic P := by
    intro Y _ _ P hP h1
    refine OddRankOneQuotient.isCyclic_of_pRank_le_one hp hp2 hP ?_
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans h1
  obtain ⟨T⟩ : Nonempty (Sylow p (↥L ⧸ Subgroup.center ↥L)) := inferInstance
  have hOut := h (↥L ⧸ Subgroup.center ↥L) hL.1.2.1 hL.1.2.2
    (S15.K7145Proof.isCatalogGroup_quotient_center hK L hq) p hp hp2 T
    (hcyc _ T.isPGroup' (S15.K7145Proof.pRank_quotient_center_le_one hp hp2 L hr.le))
  haveI : IsCyclic ↥(S.map (outerAction L)) := hcyc _ (hS.map (outerAction L)) hOut
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := ↥(S.map (outerAction L)))
  obtain ⟨s, -, hsa⟩ := Subgroup.mem_map.mp a.2
  have hCn : (Subgroup.centralizer (L : Set X)).Normal := inferInstance
  refine ⟨Subgroup.zpowers s ⊔ Subgroup.centralizer (L : Set X), le_sup_right, ?_, s,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers s), ?_⟩
  ·
    intro t ht
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (ha ⟨outerAction L t, Subgroup.mem_map_of_mem (outerAction L) ht⟩)
    have hk' : (a : Outer (↥L ⧸ Subgroup.center ↥L)) ^ k = outerAction L t := by
      simpa using congrArg Subtype.val hk
    have h1 : outerAction L (t * (s ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hsa, hk', mul_inv_cancel]
    have h2 := S15.K7145Proof.mem_sup_centralizer_of_outerAction_eq_one L h1
    have h3 : t * (s ^ k)⁻¹ * s ^ k ∈
        L ⊔ (Subgroup.zpowers s ⊔ Subgroup.centralizer (L : Set X)) :=
      Subgroup.mul_mem _ (sup_le_sup_left le_sup_right L h2)
        (Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers s k)))
    rwa [inv_mul_cancel_right] at h3
  ·
    intro w hw
    obtain ⟨y, hy, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hw
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy)
    exact ⟨n, hCn.conj_mem c hc (s ^ n)⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
