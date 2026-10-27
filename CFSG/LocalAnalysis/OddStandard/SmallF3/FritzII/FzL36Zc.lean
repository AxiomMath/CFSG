module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL36Hom

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.ABGLocalTools Certificates.FzJ36

variable {G : Type} [Group G] {t x₁ x₂ lam : G} {T₂ : Subgroup G} {a₁₂ a₂₂ a₃₂ : G}

theorem fzl_center_sq (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) {v : G} (hv : v ∈ T₂)
    (hc : ∀ g ∈ T₂, g * v = v * g) : v ^ 2 = 1 := by
  obtain ⟨π, -, -, -, -, hrange, hiff⟩ := fzl_model_hom hsh
  have hv' : v ∈ π.range := by rw [hrange]; exact hv
  obtain ⟨g, hg⟩ := Set.mem_range.mp hv'
  have hkey : KEq (g * g) 1 :=
    model_center_sq g (fun h _ => by
      apply KEq.symm
      apply (hiff (h * g) (g * h)).mp
      rw [map_mul, map_mul]
      have hhT : π h ∈ T₂ := by rw [← hrange]; exact ⟨h, rfl⟩
      have := hc (π h) hhT
      rwa [← hg] at this)
  have hgg : π (g * g) = π 1 := (hiff (g * g) 1).mpr hkey
  rw [map_mul, map_one] at hgg
  rw [hg] at hgg
  simpa [pow_two] using hgg

end CFSG.OddStandard.SmallF3.FritzII
