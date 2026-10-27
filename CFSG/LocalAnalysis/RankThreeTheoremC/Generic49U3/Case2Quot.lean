module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

theorem normalizes_of_quotient_normal {p : ℕ} {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hTM : T ≤ M)
    (h : ∀ y : ↥M ⧸ primeComplementCore (G := ↥M) p,
      ∀ t ∈ (T.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)),
        y * t * y⁻¹ ∈ (T.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p))) :
    M ≤ Subgroup.normalizer ((T ⊔ rankThreePrimeCore p M : Subgroup G) : Set G) := by
  intro g hg
  have hmem : ∀ x : ↥M, x ∈ T.subgroupOf M ⊔ primeComplementCore (G := ↥M) p ↔
      QuotientGroup.mk' (primeComplementCore (G := ↥M) p) x ∈
        (T.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)) := by
    intro x
    have h1 : T.subgroupOf M ⊔ primeComplementCore (G := ↥M) p =
        ((T.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) p))).comap
          (QuotientGroup.mk' (primeComplementCore (G := ↥M) p)) := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [h1, Subgroup.mem_comap]
  have hconj : ∀ u : ↥M, ∀ x ∈ T.subgroupOf M ⊔ primeComplementCore (G := ↥M) p,
      u * x * u⁻¹ ∈ T.subgroupOf M ⊔ primeComplementCore (G := ↥M) p := by
    intro u x hx
    rw [hmem] at hx ⊢
    have := h (QuotientGroup.mk' (primeComplementCore (G := ↥M) p) u) _ hx
    rw [map_mul, map_mul, map_inv]
    exact this
  have hS : (T ⊔ rankThreePrimeCore p M : Subgroup G) =
      (T.subgroupOf M ⊔ primeComplementCore (G := ↥M) p).map M.subtype := by
    rw [rankThreePrimeCore_eq_map_primeComplementCore, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hTM]
  have fwd : ∀ u : ↥M, ∀ x : G, x ∈ (T ⊔ rankThreePrimeCore p M : Subgroup G) →
      (u : G) * x * (u : G)⁻¹ ∈ (T ⊔ rankThreePrimeCore p M : Subgroup G) := by
    intro u x hx
    rw [hS] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨u * a * u⁻¹, hconj u a ha, by simp⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact fwd ⟨g, hg⟩ x hx
  · intro hx
    have := fwd ⟨g⁻¹, inv_mem hg⟩ _ hx
    simpa [mul_assoc] using this

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
