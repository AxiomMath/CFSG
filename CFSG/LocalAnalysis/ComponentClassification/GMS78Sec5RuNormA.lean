module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAutA
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCentG

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII

namespace Sec3.SzR

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {y d : G}

theorem normalizer_gmsA_eq
    (hS : SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : IsR₂ L T R R₂ d) (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCV : centralizer (gmsV L T : Set G) = T)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G))) :
    normalizer (gmsA L T : Set G) = normalizer (R : Set G) := by
  have hNA : normalizer (R : Set G) ≤ normalizer (gmsA L T : Set G) :=
    hS.normalizer_le_normalizer_gmsA hR₂
  refine le_antisymm (fun n hn => ?_) hNA
  have htop := hS.map_normalizer_eq_top h34 hR₂ h4 hCV hNS
  obtain ⟨⟨m, hmA⟩, hm, hmn⟩ := (htop ▸ mem_top ((gmsA L T).normalizerMonoidHom ⟨n, hn⟩) :
    (gmsA L T).normalizerMonoidHom ⟨n, hn⟩ ∈ ((normalizer (R : Set G)).subgroupOf
      (normalizer (gmsA L T : Set G))).map (gmsA L T).normalizerMonoidHom)
  have hmR : m ∈ normalizer (R : Set G) := mem_subgroupOf.mp hm
  have hc : m⁻¹ * n ∈ centralizer (gmsA L T : Set G) := by
    refine mem_centralizer_iff.mpr fun b hb => ?_
    have h1 := congrArg (fun φ : MulAut (gmsA L T) => ((φ ⟨b, hb⟩ : gmsA L T) : G)) hmn
    simp only [normalizerMonoidHom_apply_apply_coe] at h1
    calc b * (m⁻¹ * n) = m⁻¹ * (m * b * m⁻¹) * n := by group
      _ = m⁻¹ * (n * b * n⁻¹) * n := by rw [h1]
      _ = m⁻¹ * n * b := by group
  rw [hS.centralizer_gmsA_eq h34 hR₂ h4 hCV hCe hCL] at hc
  have e1 : n = m * (m⁻¹ * n) := by group
  rw [e1]
  exact mul_mem hmR (le_normalizer hc)

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
