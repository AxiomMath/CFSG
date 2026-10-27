module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25A01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

section Perp


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem omegaNbr_subset_kPerp_of_twin3 (hΩ : HypOmegaGen Ω) {A B : Subgroup G} (hB : B ∈ Ω)
    {w : G} (hwA : IsUniqueInvolution A w) (hwB : IsUniqueInvolution B w) :
    omegaNbr Ω A ⊆ KPerp Ω B := by
  rintro J ⟨hJ, hJA, R, hR, hRJ, hRN⟩
  by_cases hJB : J = B
  · exact Set.mem_insert_iff.mpr (Or.inl hJB)
  · refine Set.mem_insert_iff.mpr (Or.inr ⟨hJ, hJB, R, hR, hRJ, ?_⟩)
    obtain ⟨J', -, hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR
    exact Sec6Gen.le_normalizer_of_le_centralizer hΩ hB hJ (Ne.symm hJB) hwB hRJ hRJ'.2.1
      (by have := Sec6Gen.eight_le_of_mem_RSet hΩ hR; omega)
      (le_centralizer_of_le_normalizer hwA hRN)

theorem perp_of_twin3 {K K' : Subgroup G} {z : G} (h : Hyp23Setting Ω K K' z) {L : Subgroup G}
    (hL : L ∈ twinSet Ω K) : KPerp Ω L = {K, K'} := by
  have hLm : L ∈ ({K, K'} : Set (Subgroup G)) := h.twinSet_eq ▸ hL
  rcases hLm with hLK | hLK
  · rw [hLK]
    exact h.perp
  · rw [hLK]
    have hΩ : HypOmegaGen Ω := h.stand.hyp
    have hKΩ : K ∈ Ω := h.stand.mem
    have hK'Ω : K' ∈ Ω := h.hK'.1
    have hzK := h.hz
    have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet h.hz h.hK'
    rw [← h.perp]
    refine Set.Subset.antisymm ?_ ?_
    · exact Set.insert_subset (mem_kPerp_of_twin hΩ hK'Ω hKΩ hzK' hzK)
        (omegaNbr_subset_kPerp_of_twin3 hΩ hKΩ hzK' hzK)
    · exact Set.insert_subset (mem_kPerp_of_twin hΩ hKΩ hK'Ω hzK hzK')
        (omegaNbr_subset_kPerp_of_twin3 hΩ hK'Ω hzK hzK')

end Perp

end CFSG.ClassicalInvolution.Q3.Q3T7P24
