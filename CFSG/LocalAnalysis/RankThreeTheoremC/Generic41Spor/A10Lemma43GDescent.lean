module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem a10_descent {G : Type} [Group G] [Finite G] {M T Y' : Subgroup G} (hTM : T ≤ M) (hYM : Y' ≤ M)
    (h : (Y'.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5)) ≤
      Subgroup.normalizer (((T.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5)) :
        Subgroup (↥M ⧸ primeComplementCore (G := ↥M) 5)) : Set (↥M ⧸ primeComplementCore (G := ↥M) 5))) :
    Y' ≤ Subgroup.normalizer ((T ⊔ rankThreePrimeCore 5 M : Subgroup G) : Set G) := by
  intro g hg
  have hgM : g ∈ M := hYM hg
  have hmem : ∀ x : ↥M, x ∈ T.subgroupOf M ⊔ primeComplementCore (G := ↥M) 5 ↔
      QuotientGroup.mk' (primeComplementCore (G := ↥M) 5) x ∈
        (T.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5)) := by
    intro x
    have h1 : T.subgroupOf M ⊔ primeComplementCore (G := ↥M) 5 =
        ((T.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5))).comap
          (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5)) := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [h1, Subgroup.mem_comap]
  have hconj : ∀ u : ↥M, u ∈ Y'.subgroupOf M → ∀ x ∈ T.subgroupOf M ⊔ primeComplementCore (G := ↥M) 5,
      u * x * u⁻¹ ∈ T.subgroupOf M ⊔ primeComplementCore (G := ↥M) 5 := by
    intro u hu x hx
    rw [hmem] at hx ⊢
    have hū : QuotientGroup.mk' (primeComplementCore (G := ↥M) 5) u ∈
        Subgroup.normalizer (((T.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5)) :
          Subgroup (↥M ⧸ primeComplementCore (G := ↥M) 5)) : Set (↥M ⧸ primeComplementCore (G := ↥M) 5)) :=
      h (Subgroup.mem_map_of_mem _ hu)
    have := (Subgroup.mem_normalizer_iff.mp hū _).mp hx
    rw [map_mul, map_mul, map_inv]
    exact this
  have hS : (T ⊔ rankThreePrimeCore 5 M : Subgroup G) =
      (T.subgroupOf M ⊔ primeComplementCore (G := ↥M) 5).map M.subtype := by
    rw [rankThreePrimeCore_eq_map_primeComplementCore, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hTM]
  have fwd : ∀ u : ↥M, u ∈ Y'.subgroupOf M → ∀ x : G, x ∈ (T ⊔ rankThreePrimeCore 5 M : Subgroup G) →
      (u : G) * x * (u : G)⁻¹ ∈ (T ⊔ rankThreePrimeCore 5 M : Subgroup G) := by
    intro u hu x hx
    rw [hS] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨u * a * u⁻¹, hconj u hu a ha, by simp⟩
  have hg' : (⟨g, hgM⟩ : ↥M) ∈ Y'.subgroupOf M := hg
  have hginv : (⟨g, hgM⟩ : ↥M)⁻¹ ∈ Y'.subgroupOf M := Subgroup.inv_mem _ hg'
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact fwd ⟨g, hgM⟩ hg' x hx
  · intro hx
    have := fwd _ hginv _ hx
    simpa [mul_assoc] using this

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
