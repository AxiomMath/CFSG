module

public import CFSG.ClassicalInvolution.Asc77.ModOApi
public import CFSG.ClassicalInvolution.Asc77.WP1Section6

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem le_centralizer_of_le_normalizer {K R : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (h : R ≤ Subgroup.normalizer (K : Set G)) : R ≤ Subgroup.centralizer ({z} : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp (h hr))
  calc r * z = (r * z * r⁻¹) * r := by group
    _ = z * r := by rw [this]

omit [Finite G] in
theorem isPGroup_two_bot : IsPGroup 2 (⊥ : Subgroup G) :=
  IsPGroup.of_card (n := 0) (by simp)

theorem omegaNbr_subset_kPerp_of_twin (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K L : Subgroup G} (hL : L ∈ Ω) {z : G} (hzK : IsUniqueInvolution K z)
    (hzL : IsUniqueInvolution L z) : omegaNbr Ω K ⊆ KPerp Ω L := by
  rintro J ⟨hJ, hJK, R, hR, hRJ, hRN⟩
  by_cases hJL : J = L
  · exact Set.mem_insert_iff.mpr (Or.inl hJL)
  · refine Set.mem_insert_iff.mpr (Or.inr ⟨hJ, hJL, R, hR, hRJ, ?_⟩)
    obtain ⟨J', -, hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR
    exact hΩ.le_normalizer_of_le_centralizer hp hq hL hJ (Ne.symm hJL) hzL hRJ hRJ'.2.1
      (by have := hΩ.eight_le_of_mem_RSet hp hR; omega) (le_centralizer_of_le_normalizer hzK hRN)

theorem mem_kPerp_of_twin (hΩ : HypOmegaMod p f Ω) {K L : Subgroup G} (hK : K ∈ Ω)
    (hL : L ∈ Ω) {z : G} (hzK : IsUniqueInvolution K z) (hzL : IsUniqueInvolution L z) :
    K ∈ KPerp Ω L := by
  by_cases hKL : K = L
  · exact Set.mem_insert_iff.mpr (Or.inl hKL)
  · refine Set.mem_insert_iff.mpr (Or.inr ⟨hK, hKL, ?_⟩)
    obtain ⟨R, hR, hRK, -⟩ := exists_mem_RSet_ge hK (isPGroup_two_bot (G := G)) bot_le
    exact ⟨R, hR, hRK.1, fun x hx => hΩ.le_normalizer_of_twin hK hL hKL hzK hzL (hRK.1 hx)⟩

theorem omegaStarDiff_subset_of_twin (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω) {z : G} (hzK : IsUniqueInvolution K z)
    (hzL : IsUniqueInvolution L z) :
    omegaStarNbr Ω K \ omegaNbr Ω K ⊆ omegaStarNbr Ω L \ omegaNbr Ω L := by
  rintro J ⟨⟨hJ, hJK, U, hU, hUJ, hUN⟩, hJnot⟩
  have hJL : J ≠ L := by
    rintro rfl
    by_cases hJK' : J = K
    · exact hJK hJK'
    · apply hJnot
      have := mem_kPerp_of_twin hΩ hL hK hzL hzK
      exact (Set.mem_insert_iff.mp this).resolve_left hJK'
  refine ⟨⟨hJ, hJL, U, hU, hUJ, ?_⟩, fun h => ?_⟩
  · have h4 := (hΩ.exists_data_of_mem_USet hp hU)
    obtain ⟨R, -, J', -, hRJ', hUR, -, -, h4⟩ := h4
    exact hΩ.le_normalizer_of_le_centralizer hp hq hL hJ (Ne.symm hJL) hzL hUJ
      (hRJ'.2.1.to_le hUR) (by omega) (le_centralizer_of_le_normalizer hzK hUN)
  · have := omegaNbr_subset_kPerp_of_twin hp hq hΩ hK hzL hzK h
    exact hJnot ((Set.mem_insert_iff.mp this).resolve_left hJK)

variable (p f)

theorem l6_3 : L6_3 p f := by
  intro hp hq G _ _ Ω hΩ K hK L hL
  obtain ⟨hLΩ, z, hzK, hzL⟩ := hL
  have hKL := omegaNbr_subset_kPerp_of_twin hp hq hΩ hLΩ hzK hzL
  have hLK := omegaNbr_subset_kPerp_of_twin hp hq hΩ hK hzL hzK
  have hK' := mem_kPerp_of_twin hΩ hK hLΩ hzK hzL
  have hL' := mem_kPerp_of_twin hΩ hLΩ hK hzL hzK
  refine ⟨Set.Subset.antisymm ?_ ?_, Set.Subset.antisymm ?_ ?_⟩
  · exact Set.insert_subset hK' hKL
  · exact Set.insert_subset hL' hLK
  · exact omegaStarDiff_subset_of_twin hp hq hΩ hK hLΩ hzK hzL
  · exact omegaStarDiff_subset_of_twin hp hq hΩ hLΩ hK hzL hzK

end CFSG.ClassicalInvolution.Asc77
