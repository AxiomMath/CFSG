module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Real2
public import Certificates.Certificate22804

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.UnbalancedLayer Subgroup

theorem exists_sq_of_mem_center
    {z : Equiv.Perm (Fin 42)} (hz : z ∈ T0) (hzc : ∀ t ∈ T0, z * t = t * z) :
    ∃ d ∈ T0, d * d = z := by
  have h := Certificates.certificate22804
  rw [sqCenterOK, List.all_eq_true] at h
  have h1 := h _ ((mem_T0_iff z).1 hz)
  rw [(inZB_iff z).2 ⟨hz, hzc⟩, Bool.not_true, Bool.false_or, List.any_eq_true] at h1
  obtain ⟨c, hc, hce⟩ := h1
  obtain ⟨d, hd, rfl⟩ := exists_of_mem_t0L hc
  refine ⟨d, hd, ?_⟩
  rw [Nat.beq_eq, psq_code, code_inj] at hce
  exact hce

namespace Real

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} (ρ : Real K)

include ρ in
theorem exists_sq_of_center
    {Sg : Subgroup G}
    (hS : IsSylowTwoIn Sg (normalizer (K : Set G))) {a : G}
    (ha : a ∈ Sg ⊓ K ⊓ centralizer ((Sg ⊓ K : Subgroup G) : Set G)) :
    ∃ g ∈ Sg ⊓ K, a⁻¹ * (g * g) ∈ coreActionKernel K := by
  have hSN := hS.1
  have hS2 := GrS4.isPGroup_of_isSylowTwoIn hS
  obtain ⟨heq, h64⟩ := ρ.img_inf_K_eq hS
  obtain ⟨c, -, -, hiff, hsurj⟩ := exists_std (ρ.img_le_R Sg) (ρ.img_isPGroup hS2) h64
  obtain ⟨⟨haS, haK⟩, hac⟩ := mem_inf.1 ha
  set a' : ↥(normalizer (K : Set G)) := ⟨a, hSN haS⟩
  have ha' : ρ.φ a' ∈ ρ.img Sg ⊓ S := heq ▸ ρ.phi_mem_img (mem_inf.2 ⟨haS, haK⟩)
  have hac' : ∀ s ∈ ρ.img Sg ⊓ S, ρ.φ a' * s = s * ρ.φ a' := by
    intro s hs
    rw [← heq] at hs
    obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 hs
    rw [← map_mul, ← map_mul]
    exact congrArg ρ.φ (Subtype.ext (mem_centralizer_iff.1 hac g hg).symm)
  have hzT : c * ρ.φ a' * c⁻¹ ∈ T0 := (hiff _ (mem_inf.1 ha').1).1 (mem_inf.1 ha').2
  have hzc : ∀ t ∈ T0, c * ρ.φ a' * c⁻¹ * t = t * (c * ρ.φ a' * c⁻¹) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := hsurj t ht
    rw [show c * ρ.φ a' * c⁻¹ * (c * s * c⁻¹) = c * (ρ.φ a' * s) * c⁻¹ by group, hac' s hs]
    group
  obtain ⟨d, hd, hdd⟩ := exists_sq_of_mem_center hzT hzc
  obtain ⟨x, hx, rfl⟩ := hsurj d hd
  rw [← heq] at hx
  obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 hx
  refine ⟨g, hg, ?_⟩
  have h1 : ρ.φ (g * g) = ρ.φ a' := by
    rw [show c * ρ.φ g * c⁻¹ * (c * ρ.φ g * c⁻¹) = c * (ρ.φ g * ρ.φ g) * c⁻¹ by group] at hdd
    rw [map_mul]
    simpa using hdd
  have h2 : ρ.φ (a'⁻¹ * (g * g)) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
  exact (ρ.ker_iff _).1 h2

end Real

end CFSG.ComponentClassification.HSFLit.AutL34
