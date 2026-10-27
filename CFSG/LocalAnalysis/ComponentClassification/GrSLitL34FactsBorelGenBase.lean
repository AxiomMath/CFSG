
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCentralFourModelBase

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj {H : Subgroup G} {x : G} (h1 : ∀ g ∈ H, x * g * x⁻¹ ∈ H)
    (h2 : ∀ g ∈ H, x⁻¹ * g * x ∈ H) : x ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  refine ⟨h1 g, fun hg => ?_⟩
  have := h2 _ hg
  rwa [show x⁻¹ * (x * g * x⁻¹) * x = g by group] at this

private theorem D4_pow_four :
    ∀ d : Multiplicative (ZMod 4) × Multiplicative (ZMod 4), d ^ 4 = 1 := by
  decide

theorem conj_mem_Z0 {s : Equiv.Perm (Fin 42)}
    (hs : s ∈ normalizer (T0 : Set (Equiv.Perm (Fin 42)))) {t : Equiv.Perm (Fin 42)}
    (ht : t ∈ Z0) : s * t * s⁻¹ ∈ Z0 := by
  obtain ⟨hc, hT⟩ := ht
  refine ⟨mem_centralizer_iff.mpr fun t' ht' => ?_, (mem_normalizer_iff.mp hs t).mp hT⟩
  have h1 : s⁻¹ * t' * s ∈ T0 := by
    have := (mem_normalizer_iff.mp (inv_mem hs) t').mp ht'
    rwa [inv_inv] at this
  have h2 := (mem_centralizer_iff.mp hc) _ h1
  calc t' * (s * t * s⁻¹) = s * ((s⁻¹ * t' * s) * t) * s⁻¹ := by group
    _ = s * (t * (s⁻¹ * t' * s)) * s⁻¹ := by rw [h2]
    _ = s * t * s⁻¹ * t' := by group

end CFSG.ComponentClassification.GrSLit.L34Facts
