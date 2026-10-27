module

public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open scoped Pointwise

variable {G : Type*} [Group G]

theorem eq_inf_sup_of_le_sup_of_le_normalizer {Λ R M : Subgroup G}
    (hMR : M ≤ normalizer (R : Set G)) (hMΛ : M ≤ Λ) (hΛ : Λ ≤ R ⊔ M) : Λ = (Λ ⊓ R) ⊔ M := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left hMΛ)
  have hx' : x ∈ ((R ⊔ M : Subgroup G) : Set G) := hΛ hx
  rw [coe_mul_of_right_le_normalizer_left R M hMR] at hx'
  obtain ⟨r, hr, m, hm, rfl⟩ := hx'
  have hrΛ : r ∈ Λ := by
    have : r * m * m⁻¹ ∈ Λ := mul_mem hx (inv_mem (hMΛ hm))
    simpa using this
  exact mul_mem (mem_sup_left (mem_inf.2 ⟨hrΛ, hr⟩)) (mem_sup_right hm)

theorem perfectCore_eq_inf_sup_of_le_sup {C R M : Subgroup G}
    (hMR : M ≤ normalizer (R : Set G)) (hM : ⁅M, M⁆ = M) (hMC : M ≤ C)
    (hle : perfectCore C ≤ R ⊔ M) :
    perfectCore C = (perfectCore C ⊓ R) ⊔ M :=
  eq_inf_sup_of_le_sup_of_le_normalizer hMR (le_perfectCore_of_perfect hMC hM) hle

theorem le_normalizer_inf_of_le_of_le_normalizer {Λ R M : Subgroup G}
    (hMR : M ≤ normalizer (R : Set G)) (hMΛ : M ≤ Λ) :
    M ≤ normalizer ((Λ ⊓ R : Subgroup G) : Set G) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro h
  have hΛ := (mem_normalizer_iff.1 (le_normalizer (hMΛ hm))) h
  have hR := (mem_normalizer_iff.1 (hMR hm)) h
  simp only [mem_inf] at hΛ hR ⊢
  exact ⟨fun ⟨h1, h2⟩ => ⟨hΛ.1 h1, hR.1 h2⟩, fun ⟨h1, h2⟩ => ⟨hΛ.2 h1, hR.2 h2⟩⟩

theorem disjoint_inf_of_disjoint {Λ R M : Subgroup G} (hRM : Disjoint R M) :
    Disjoint (Λ ⊓ R) M :=
  hRM.mono_left inf_le_right

end CFSG.SeitzReduction.EPilot
