module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerIsoCorrSylowGrowth

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_mem_of_sylow {H S : Subgroup G} {t : G}
    (hS : ∃ P : Sylow 2 ↥H, (P : Subgroup ↥H) = S.subgroupOf H) (ht : t ∈ H)
    (ht2 : orderOf t = 2) : ∃ g ∈ H, g⁻¹ * t * g ∈ S := by
  have hP : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  obtain ⟨g, hg, hle⟩ := exists_conjugate_le_of_sylow hS (zpowers_le.mpr ht) hP
  exact ⟨g, hg, hle (conj_mem_conjugate (mem_zpowers t) g)⟩

omit [Finite G] in
theorem conjugate_map_pPrimeCore_centralizer (x h : G) :
    conjugate ((pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype)
        h =
      (pPrimeCore 2 (centralizer ({h⁻¹ * x * h} : Set G))).map
        (centralizer ({h⁻¹ * x * h} : Set G)).subtype := by
  have h1 := map_pPrimeCore_centralizer_of_mulAut (MulAut.conj h⁻¹) x
  rw [MulAut.conj_apply, inv_inv] at h1
  exact h1

end CFSG.ComponentClassification.UnbalancedCorr
