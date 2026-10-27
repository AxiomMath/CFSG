module

public import CFSG.ClassicalInvolution.Phan.PhanS7Def
import all CFSG.ClassicalInvolution.Phan.PhanH5Frames

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

section Formula

variable {F : Type} [Field F] (h2 : (2 : F) ≠ 0)

theorem La1_mk7 (A : SL(2, F)) (x0 x1 x2 y0 y1 y2 z : F) :
    La1 h2 A (mk7 x0 x1 x2 y0 y1 y2 z) =
      mk7 x0 (A 0 0 * x1 + 2 * A 0 1 * x2) (A 1 0 * x1 / 2 + A 1 1 * x2) y0
        (A 1 1 * y1 - A 1 0 * y2 / 2) (A 0 0 * y2 - 2 * A 0 1 * y1) z := by
  have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  rw [La1, Frame.La_apply]
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i
    all_goals simp [Frame.incl_apply, Frame.coords_apply, HypFrame.toFrame, Frame.e₁, Frame.f₁,
      Frame.e₂, Frame.f₂, hyp1, polar_mk7, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals field_simp
    all_goals ring
  · fin_cases i
    all_goals simp [Frame.incl_apply, Frame.coords_apply, HypFrame.toFrame, Frame.e₁, Frame.f₁,
      Frame.e₂, Frame.f₂, hyp1, polar_mk7, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals field_simp
    all_goals ring
  · simp [Frame.incl_apply, Frame.coords_apply, HypFrame.toFrame, Frame.e₁, Frame.f₁, Frame.e₂,
      Frame.f₂, hyp1, polar_mk7, Matrix.mul_apply, Fin.sum_univ_two]

theorem La1_apply (A : SL(2, F)) (x : W7 F) :
    La1 h2 A x = mk7 (x (.inl 0)) (A 0 0 * x (.inl 1) + 2 * A 0 1 * x (.inl 2))
      (A 1 0 * x (.inl 1) / 2 + A 1 1 * x (.inl 2)) (x (.inr (.inl 0)))
      (A 1 1 * x (.inr (.inl 1)) - A 1 0 * x (.inr (.inl 2)) / 2)
      (A 0 0 * x (.inr (.inl 2)) - 2 * A 0 1 * x (.inr (.inl 1))) (x (.inr (.inr ()))) := by
  conv_lhs => rw [mk7_eta x]
  exact La1_mk7 h2 A _ _ _ _ _ _ _

namespace HA1

theorem fr1_e₁_eq : (fr1 h2).e₁ = mk7 0 2 0 0 0 0 0 := by
  simp [fr1, hyp1, HypFrame.toFrame, Frame.e₁]

theorem fr1_f₁_eq : (fr1 h2).f₁ = mk7 0 0 0 0 (1 / 2) 0 0 := by
  simp [fr1, hyp1, HypFrame.toFrame, Frame.f₁]

theorem fr1_e₂_eq : (fr1 h2).e₂ = mk7 0 0 0 0 0 1 0 := by
  simp [fr1, hyp1, HypFrame.toFrame, Frame.e₂]

theorem fr1_f₂_eq : (fr1 h2).f₂ = mk7 0 0 1 0 0 0 0 := by
  simp [fr1, hyp1, HypFrame.toFrame, Frame.f₂]

end HA1

end Formula

section Extension

variable {F K : Type} [Field F] [Field K] [Algebra F K] (h2 : (2 : F) ≠ 0)

namespace HA1

theorem extK_apply (f : W7 F →ₗ[F] W7 F) (x : W7 K) (s : Fin 3 ⊕ Fin 3 ⊕ Unit) :
    extK f x s = ∑ t, algebraMap F K (f (Pi.single t 1) s) * x t := by
  simp [extK, Matrix.mulVec, dotProduct, LinearMap.toMatrix'_apply]

end HA1

theorem extK_La1_mk7 (A : SL(2, F)) (x0 x1 x2 y0 y1 y2 z : K) :
    extK (La1 h2 A).toLinearMap (mk7 x0 x1 x2 y0 y1 y2 z) =
      mk7 x0 (algebraMap F K (A 0 0) * x1 + 2 * algebraMap F K (A 0 1) * x2)
        (algebraMap F K (A 1 0) * x1 / 2 + algebraMap F K (A 1 1) * x2) y0
        (algebraMap F K (A 1 1) * y1 - algebraMap F K (A 1 0) * y2 / 2)
        (algebraMap F K (A 0 0) * y2 - 2 * algebraMap F K (A 0 1) * y1) z := by
  funext s
  rw [HA1.extK_apply]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_three, Finset.univ_unique, Finset.sum_singleton]
  rcases s with i | i | ⟨⟩
  · fin_cases i
    all_goals simp [La1_apply, map_ofNat]
    all_goals ring
  · fin_cases i
    all_goals simp [La1_apply, map_ofNat]
    all_goals ring
  · simp [La1_apply]

end Extension

end CFSG.ClassicalInvolution.PhanB3.S
