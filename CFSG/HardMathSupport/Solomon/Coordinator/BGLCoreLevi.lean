module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreLevel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.LargeExtraspecial.A2Mod

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem mem_of_mul_eq {G : Type*} [Group G] {H : Subgroup G} {g y w : G} (hg : g ∈ H)
    (hy : y ∈ H) (h : g * y = w * y * g) : w ∈ H := by
  have hw : w * y ∈ H := mem_of_conj hg hy h
  have : w = w * y * y⁻¹ := by group
  rw [this]
  exact H.mul_mem hw (H.inv_mem hy)

section Levi

variable {H : Subgroup (SpecialLinearGroup (Fin 3) F)} (hA : fixSL3 σ ≤ H)
include hA

theorem top_le_of_levi [Finite F] (hr : (orderOf σ).Prime) {s t : F}
    (hst : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) s *
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t ∈ H)
    (hnr : ¬ (σ s = s ∧ σ t = t)) : ⊤ ≤ H := by
  have e1 : SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : F) *
      (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) s *
        SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t) =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (-s) *
        (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) s *
          SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t) *
        SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : F) := by
    apply Subtype.ext
    simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]
  have e2 : SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : F) *
      (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) s *
        SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t) =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (-t) *
        (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) s *
          SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t) *
        SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : F) := by
    apply Subtype.ext
    simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]
  have h1 := mem_of_mul_eq (hA (transvection_mem_fixSL3 _ (map_one σ))) hst e1
  have h2 := mem_of_mul_eq (hA (transvection_mem_fixSL3 _ (map_one σ))) hst e2
  by_cases hs : σ s = s
  · have ht : σ t ≠ t := fun ht => hnr ⟨hs, ht⟩
    exact top_le_of_x01 hA hr h2 (by rw [map_neg]; exact fun h => ht (neg_injective h))
  · exact top_le_of_x02 hA hr h1 (by rw [map_neg]; exact fun h => hs (neg_injective h))

theorem top_le_of_dualLevi [Finite F] (hr : (orderOf σ).Prime) {y₀ y₁ : F}
    (hy : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) y₀ *
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) y₁ ∈ H)
    (hnr : ¬ (σ y₀ = y₀ ∧ σ y₁ = y₁)) : ⊤ ≤ H := by
  have e1 : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F) *
      (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) y₀ *
        SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) y₁) =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) y₁ *
        (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) y₀ *
          SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) y₁) *
        SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F) := by
    apply Subtype.ext
    simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]
  have e2 : SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
      (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) y₀ *
        SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) y₁) =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) y₀ *
        (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) y₀ *
          SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) y₁) *
        SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : F) := by
    apply Subtype.ext
    simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]
    all_goals ring
  have h1 := mem_of_mul_eq (hA (transvection_mem_fixSL3 _ (map_one σ))) hy e1
  have h2 := mem_of_mul_eq (hA (transvection_mem_fixSL3 _ (map_one σ))) hy e2
  by_cases h0 : σ y₀ = y₀
  · exact top_le_of_x02 hA hr h1 (fun h => hnr ⟨h0, h⟩)
  · exact top_le_of_x12 hA hr h2 h0

end Levi

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
