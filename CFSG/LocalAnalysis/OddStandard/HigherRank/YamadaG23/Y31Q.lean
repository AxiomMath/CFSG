module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Fus1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31NT
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31KSa
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31KSb

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_Q_eq (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) :
    s.T ⊓ centralizer (L : Set G) = zpowers s.t := by
  refine le_antisymm ?_ (Subgroup.zpowers_le.mpr (s3_t_mem_Q s))
  intro q hq
  by_contra hqnot
  have hQ : ∃ q ∈ s.T ⊓ centralizer (L : Set G), q ∉ zpowers s.t := ⟨q, hq, hqnot⟩
  have hNTfix : ∀ n ∈ normalizer (s.T : Set G), n * s.t * n⁻¹ = s.t := by
    intro n hn
    by_cases hRT : s.R = s.T
    · exact s3_NT_fix_t_RT s hS hZ hRT hQ n hn
    · exact s3_NT_fix_t_RneT s hS hZ hOut hRT hQ n hn
  have hz_mem : s.fr.z ∈ zt s := Subgroup.subset_closure (by simp)
  obtain ⟨g, hg | hg⟩ := s3_fusion_zt s hS hZ hOut
  ·
    have hg_cen : g * s.t * g⁻¹ ∈ cen s.T := by
      rw [hg]
      exact (s3_zt_le_cen_T s hS hZ) hz_mem
    obtain ⟨n, hn, hnz⟩ := s3_fusion_NT s hg_cen
    rw [hg] at hnz
    have hfix : n⁻¹ * s.t * n = s.t := by
      simpa using hNTfix n⁻¹ (inv_mem hn)
    have hz : s.fr.z = s.t := by
      have h1 : n⁻¹ * (n * s.fr.z * n⁻¹) * n = n⁻¹ * s.t * n :=
        congrArg (fun x => n⁻¹ * x * n) hnz
      rw [hfix] at h1
      simpa [mul_assoc] using h1
    exact s3_t_not_mem_L_of_odd s hZ (hz ▸ s3_z_mem_L s)
  ·
    have hzt_mem : s.fr.z * s.t ∈ zt s := mul_mem hz_mem (Subgroup.subset_closure (by simp))
    have hg_cen : g * s.t * g⁻¹ ∈ cen s.T := by
      rw [hg]
      exact (s3_zt_le_cen_T s hS hZ) hzt_mem
    obtain ⟨n, hn, hnz⟩ := s3_fusion_NT s hg_cen
    rw [hg] at hnz
    have hfix : n⁻¹ * s.t * n = s.t := by
      simpa using hNTfix n⁻¹ (inv_mem hn)
    have hzt : s.fr.z * s.t = s.t := by
      have h1 : n⁻¹ * (n * (s.fr.z * s.t) * n⁻¹) * n = n⁻¹ * s.t * n :=
        congrArg (fun x => n⁻¹ * x * n) hnz
      rw [hfix] at h1
      simpa [mul_assoc] using h1
    have hz1 : s.fr.z = 1 := by
      have h := congrArg (fun x => x * s.t⁻¹) hzt
      simpa [mul_assoc] using h
    have hA : LFactsA s := lfactsA_of_setting hS hZ s
    have hord := s3_z_order s hA
    rw [hz1, orderOf_one] at hord
    norm_num at hord

end CFSG.OddStandard.HigherRank.YamadaG23
