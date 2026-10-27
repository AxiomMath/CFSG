module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandardBase

public section

namespace CFSG.ComponentClassification.HSFLit.AutBeta

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.UnbalancedLayer Subgroup

variable {G : Type} [Group G]

theorem betaHat_mem_K (K : Subgroup G) {k : G} (hk : k ∈ K) (e : Jhat K) :
    betaHat K (le_normalizer hk) e = (jq K ⟨k, hk⟩)⁻¹ * e * jq K ⟨k, hk⟩ := by
  obtain ⟨j, rfl⟩ := jq_surjective K e
  rw [betaHat_jq, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem betaHat_eq_id_iff (K : Subgroup G) {g : G} (hg : g ∈ normalizer (K : Set G)) :
    (∀ e, betaHat K hg e = e) ↔ g ∈ coreActionKernel K := by
  constructor
  · intro h
    refine ⟨hg, fun j hj => ?_⟩
    have hm : j⁻¹ * g⁻¹ * j * g ∈ K := by
      have := conj_mem_of_mem_normalizer hg hj
      rw [show j⁻¹ * g⁻¹ * j * g = j⁻¹ * (g⁻¹ * j * g) by group]
      exact K.mul_mem (K.inv_mem hj) this
    show _ ∈ oddIn K
    rw [mem_oddIn_iff hm]
    have e1 : (⟨j⁻¹ * g⁻¹ * j * g, hm⟩ : K) = (⟨j, hj⟩ : K)⁻¹ * conjJ K hg ⟨j, hj⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
      group
    rw [e1, map_mul, map_inv, ← betaHat_jq, h, inv_mul_cancel]
  · rintro ⟨-, h⟩ e
    obtain ⟨j, rfl⟩ := jq_surjective K e
    rw [betaHat_jq]
    have hm : (j : G)⁻¹ * g⁻¹ * j * g ∈ K := by
      have := conj_mem_of_mem_normalizer hg j.2
      rw [show (j : G)⁻¹ * g⁻¹ * j * g = (j : G)⁻¹ * (g⁻¹ * j * g) by group]
      exact K.mul_mem (K.inv_mem j.2) this
    have h1 := (mem_oddIn_iff hm).1 (h j j.2)
    have e1 : (⟨(j : G)⁻¹ * g⁻¹ * j * g, hm⟩ : K) = j⁻¹ * conjJ K hg j := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
      group
    rw [e1, map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm

end CFSG.ComponentClassification.HSFLit.AutBeta
