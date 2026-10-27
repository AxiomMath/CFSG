module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25Datum

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof

open Subgroup CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof

variable {G : Type*} [Group G]

theorem conj_zpow_of_mem_normalizer {y p : G} (hy : orderOf y = 4)
    (hp : p ∈ normalizer ((zpowers y : Subgroup G) : Set G)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ i : ℤ, p * y ^ i * p⁻¹ = y ^ (ε * i) := by
  rcases conj_eq_or_eq_inv_of_mem_normalizer hy hp with h | h
  · refine ⟨1, Or.inl rfl, fun i => ?_⟩
    rw [← conj_zpow, h]; simp
  · refine ⟨-1, Or.inr rfl, fun i => ?_⟩
    rw [← conj_zpow, h]; simp [zpow_neg, inv_zpow']

theorem conj_inv_zpow_of_mem_normalizer {y p : G} (hy : orderOf y = 4)
    (hp : p ∈ normalizer ((zpowers y : Subgroup G) : Set G)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (∀ i : ℤ, p * y ^ i * p⁻¹ = y ^ (ε * i)) ∧
      ∀ i : ℤ, p⁻¹ * y ^ i * p = y ^ (ε * i) := by
  obtain ⟨ε, hε, h⟩ := conj_zpow_of_mem_normalizer hy hp
  refine ⟨ε, hε, h, fun i => ?_⟩
  have h2 := h (ε * i)
  have hεε : ε * (ε * i) = i := by rcases hε with rfl | rfl <;> ring
  rw [hεε] at h2
  calc p⁻¹ * y ^ i * p = p⁻¹ * (p * y ^ (ε * i) * p⁻¹) * p := by rw [h2]
    _ = y ^ (ε * i) := by group

theorem commutator_le_centralizer_of_normalizer {S : Subgroup G} {y : G} (hy : orderOf y = 4)
    (hS : S ≤ normalizer ((zpowers y : Subgroup G) : Set G)) :
    ⁅S, S⁆ ≤ centralizer ({y} : Set G) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [mem_centralizer_singleton_iff]
  obtain ⟨ε, hε, hεa, hεa'⟩ := conj_inv_zpow_of_mem_normalizer hy (hS ha)
  obtain ⟨δ, hδ, hδb, hδb'⟩ := conj_inv_zpow_of_mem_normalizer hy (hS hb)
  have key : a * b * a⁻¹ * b⁻¹ * y * (b * a * b⁻¹ * a⁻¹) = y := by
    have h1 : b⁻¹ * y * b = y ^ δ := by simpa using hδb' 1
    have h2 : a⁻¹ * y ^ δ * a = y ^ (ε * δ) := hεa' δ
    have h3 : b * y ^ (ε * δ) * b⁻¹ = y ^ (δ * (ε * δ)) := hδb (ε * δ)
    have h4 : a * y ^ (δ * (ε * δ)) * a⁻¹ = y ^ (ε * (δ * (ε * δ))) := hεa _
    have hε1 : ε * (δ * (ε * δ)) = 1 := by
      rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> ring
    calc a * b * a⁻¹ * b⁻¹ * y * (b * a * b⁻¹ * a⁻¹)
        = a * (b * (a⁻¹ * (b⁻¹ * y * b) * a) * b⁻¹) * a⁻¹ := by group
      _ = y := by rw [h1, h2, h3, h4, hε1]; simp
  rw [commutatorElement_def]
  calc a * b * a⁻¹ * b⁻¹ * y
      = (a * b * a⁻¹ * b⁻¹ * y * (b * a * b⁻¹ * a⁻¹)) * (a * b * a⁻¹ * b⁻¹) := by group
    _ = y * (a * b * a⁻¹ * b⁻¹) := by rw [key]

end CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof
