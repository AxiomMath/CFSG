module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Subgroup

theorem exists_mem_centralizer_not_mem_normalizer {G : Type*} [Group G]
    (R Y : Subgroup G) (hNY : Subgroup.normalizer (R : Set G) ≤ Y) (y : G) (hy : y ∈ Y)
    (hyN : y ∉ Subgroup.normalizer (R : Set G)) (R' : Subgroup G) (hR' : ∀ x : G, x ∈ R' ↔ y⁻¹ * x * y ∈ R)
    (t : G) (ht : t ∈ Subgroup.normalizer (R' : Set G))
    (hfuse : ∀ s ∈ Subgroup.normalizer (R : Set G), IsConj t s → ∃ m ∈ Subgroup.normalizer (R : Set G), m * t * m⁻¹ = s) :
    ∃ w ∈ Y, w ∈ Subgroup.centralizer {t} ∧ w ∉ Subgroup.normalizer (R : Set G) := by
  have hs : y⁻¹ * t * y ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro r
    have h3 := (Subgroup.mem_normalizer_iff.mp ht) (y * r * y⁻¹)
    rw [hR', hR'] at h3
    have e1 : y⁻¹ * (y * r * y⁻¹) * y = r := by group
    have e2 : y⁻¹ * (t * (y * r * y⁻¹) * t⁻¹) * y = (y⁻¹ * t * y) * r * (y⁻¹ * t * y)⁻¹ := by
      group
    rw [e1, e2] at h3
    exact h3
  have hconj : IsConj t (y⁻¹ * t * y) := isConj_iff.mpr ⟨y⁻¹, by group⟩
  obtain ⟨m, hm, hmeq⟩ := hfuse (y⁻¹ * t * y) hs hconj
  refine ⟨y * m, Y.mul_mem hy (hNY hm), ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hty : t * y = y * (m * t * m⁻¹) := by
      calc t * y = y * (y⁻¹ * t * y) := by group
        _ = y * (m * t * m⁻¹) := by rw [hmeq]
    calc y * m * t = (y * (m * t * m⁻¹)) * m := by group
      _ = (t * y) * m := by rw [← hty]
      _ = t * (y * m) := by group
  · intro hw
    apply hyN
    have := (Subgroup.normalizer (R : Set G)).mul_mem hw
      ((Subgroup.normalizer (R : Set G)).inv_mem hm)
    simpa using this

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
