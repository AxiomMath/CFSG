module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect)

variable {G : Type*} [Group G]

theorem mem_conjugate_iff_of_mul {G₀ : Subgroup G} {h x : G} :
    x ∈ CFSG.conjugate G₀ h ↔ h * x * h⁻¹ ∈ G₀ := by
  change x ∈ G₀.map (MulAut.conj h⁻¹).toMonoidHom ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    refine ⟨h * x * h⁻¹, hx, ?_⟩
    simp [mul_assoc]

theorem mem_normalizer_conjugate_of_conj_mem_normalizer {G₀ : Subgroup G} {t g : G}
    (h : g⁻¹ * t * g ∈ normalizer (G₀ : Set G)) :
    t ∈ normalizer (CFSG.conjugate G₀ g⁻¹ : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [mem_conjugate_iff_of_mul, mem_conjugate_iff_of_mul, inv_inv]
  have e : g⁻¹ * (t * x * t⁻¹) * g =
      (g⁻¹ * t * g) * (g⁻¹ * x * g) * (g⁻¹ * t * g)⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.1 h _)

theorem unique_of_forall_conjugate_eq {G₀ : Subgroup G} {t : G}
    (h : ∀ g : G, t ∈ normalizer (CFSG.conjugate G₀ g : Set G) → CFSG.conjugate G₀ g = G₀) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G) := by
  intro g hg
  have hM := h g⁻¹ (mem_normalizer_conjugate_of_conj_mem_normalizer hg)
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : g * x * g⁻¹ ∈ CFSG.conjugate G₀ g⁻¹ := by
      rw [mem_conjugate_iff_of_mul, inv_inv]
      simpa [mul_assoc] using hx
    rwa [hM] at hx'
  · intro hx
    rw [← hM, mem_conjugate_iff_of_mul, inv_inv] at hx
    simpa [mul_assoc] using hx

variable [Finite G]

theorem eq_of_le_iSup_perfectCore {ι : Type*} {M G₀ : Subgroup G} {J : ι → Subgroup G}
    (hgen : M ≤ ⨆ i, perfectCore (M ⊓ centralizer (J i : Set G)))
    (hJ : ∀ i, centralizerPerfectCore (J i) ≤ G₀) (hcard : Nat.card G₀ ≤ Nat.card M) :
    M = G₀ := by
  have hle : M ≤ G₀ := hgen.trans (iSup_le fun i =>
    (le_centralizerPerfectCore (perfectCore_perfect _)
      ((perfectCore_le _).trans inf_le_right)).trans (hJ i))
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem unique_of_forall_conjugate_generation {ι : Type*} {G₀ : Subgroup G} {t : G}
    {J : ι → Subgroup G} (hJ : ∀ i, centralizerPerfectCore (J i) ≤ G₀)
    (hgen : ∀ h : G, t ∈ normalizer (CFSG.conjugate G₀ h : Set G) →
      CFSG.conjugate G₀ h ≤
        ⨆ i, perfectCore (CFSG.conjugate G₀ h ⊓ centralizer (J i : Set G))) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G) :=
  unique_of_forall_conjugate_eq fun h ht => eq_of_le_iSup_perfectCore (hgen h ht) hJ
    (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).symm)

end CFSG.SeitzReduction.F4Pilot
