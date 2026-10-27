module

public import CFSG.ClassicalInvolution.Phan.PhanS13CVec
import CFSG.ClassicalInvolution.Asc77.AscT7HS1

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H

section Swap

variable {F : Type} [Field F]

theorem det_swap_ne_one (h2 : (2 : F) ≠ 0) (φ : W7 F ≃ₗ[F] W7 F)
    (hφ : ∀ x, φ x = x ∘ Equiv.swap (Sum.inl 0 : Fin 3 ⊕ Fin 3 ⊕ Unit) (Sum.inr (Sum.inl 0))) :
    LinearEquiv.det φ ≠ 1 := by
  intro hdet
  have h1 : (φ : W7 F →ₗ[F] W7 F) = Matrix.toLin'
      ((Equiv.swap (Sum.inl 0 : Fin 3 ⊕ Fin 3 ⊕ Unit) (Sum.inr (Sum.inl 0))).permMatrix F) := by
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec]
    exact hφ x
  have h3 : LinearMap.det (φ : W7 F →ₗ[F] W7 F) = 1 := by
    rw [← LinearEquiv.coe_det, hdet]
    rfl
  rw [h1, LinearMap.det_toLin', Matrix.det_permutation, Equiv.Perm.sign_swap (by simp)] at h3
  have h4 : (-1 : F) = 1 := by simpa using h3
  exact h2 (by linear_combination (-1 : F) * h4)

end Swap

section Fix6

variable {F : Type} [Field F]

theorem eq_one_or_swap_of_fix_six (h2 : (2 : F) ≠ 0) (g : spinGroup (quadOdd 3 F))
    (a1 : spinAction (quadOdd 3 F) g (mk7 1 0 0 1 0 0 0) = mk7 1 0 0 1 0 0 0)
    (a2 : spinAction (quadOdd 3 F) g (mk7 0 0 0 0 0 0 1) = mk7 0 0 0 0 0 0 1)
    (a3 : spinAction (quadOdd 3 F) g (mk7 0 1 0 0 (-1) 0 0) = mk7 0 1 0 0 (-1) 0 0)
    (a4 : spinAction (quadOdd 3 F) g (mk7 0 0 1 0 0 (-1) 0) = mk7 0 0 1 0 0 (-1) 0)
    (a5 : spinAction (quadOdd 3 F) g (mk7 0 1 0 0 1 0 0) = mk7 0 1 0 0 1 0 0)
    (a6 : spinAction (quadOdd 3 F) g (mk7 0 0 1 0 0 1 0) = mk7 0 0 1 0 0 1 0) :
    (∀ x, spinAction (quadOdd 3 F) g x = x) ∨
      ∀ x, spinAction (quadOdd 3 F) g x =
        x ∘ Equiv.swap (Sum.inl 0 : Fin 3 ⊕ Fin 3 ⊕ Unit) (Sum.inr (Sum.inl 0)) := by
  have hpol : ∀ w, spinAction (quadOdd 3 F) g w = w →
      polar (quadOdd 3 F) (spinAction (quadOdd 3 F) g (mk7 1 0 0 (-1) 0 0 0)) w =
        polar (quadOdd 3 F) (mk7 1 0 0 (-1) 0 0 0) w := by
    intro w hw
    have := polar_spinAction (quadOdd 3 F) g (mk7 1 0 0 (-1) 0 0 0) w
    rwa [hw] at this
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, hy⟩ : ∃ y0 y1 y2 y3 y4 y5 y6 : F,
      spinAction (quadOdd 3 F) g (mk7 1 0 0 (-1) 0 0 0) = mk7 y0 y1 y2 y3 y4 y5 y6 :=
    ⟨_, _, _, _, _, _, _, mk7_eta _⟩
  have e1 := hpol _ a1
  have e2 := hpol _ a2
  have e3 := hpol _ a3
  have e4 := hpol _ a4
  have e5 := hpol _ a5
  have e6 := hpol _ a6
  rw [hy] at e1 e2 e3 e4 e5 e6
  simp only [polar_mk7] at e1 e2 e3 e4 e5 e6
  have hq := map_spinAction (quadOdd 3 F) g (mk7 1 0 0 (-1) 0 0 0)
  rw [hy] at hq
  simp only [quad_mk7] at hq
  have z6 : y6 = 0 := (mul_eq_zero.mp (by linear_combination e2 : 2 * y6 = 0)).resolve_left h2
  have z1 : y1 = 0 :=
    (mul_eq_zero.mp (by linear_combination e5 - e3 : 2 * y1 = 0)).resolve_left h2
  have z2 : y2 = 0 :=
    (mul_eq_zero.mp (by linear_combination e6 - e4 : 2 * y2 = 0)).resolve_left h2
  have z4 : y4 = 0 := by linear_combination e5 - z1
  have z5 : y5 = 0 := by linear_combination e6 - z2
  have z3 : y3 = -y0 := by linear_combination e1
  have hsq : y0 * y0 = 1 := by
    rw [z1, z2, z3, z4, z5, z6] at hq
    linear_combination -hq
  have hform : ∀ x0 x1 x2 u0 u1 u2 z : F, spinAction (quadOdd 3 F) g (mk7 x0 x1 x2 u0 u1 u2 z) =
      mk7 (((1 + y0) / 2) * x0 + ((1 - y0) / 2) * u0) x1 x2
        (((1 - y0) / 2) * x0 + ((1 + y0) / 2) * u0) u1 u2 z := by
    intro x0 x1 x2 u0 u1 u2 z
    rw [mk7_decomp7 h2 x0 x1 x2 u0 u1 u2 z]
    simp only [map_add, map_smul, a1, a2, a3, a4, a5, a6, hy, z1, z2, z3, z4, z5, z6]
    funext t
    rcases t with i | i | u
    · fin_cases i <;> simp [mk7] <;> field_simp <;> ring
    · fin_cases i <;> simp [mk7] <;> field_simp <;> ring
    · simp [mk7]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · left
    have c1 : (1 + y0) / 2 = 1 := by rw [h, one_add_one_eq_two, div_self h2]
    have c2 : (1 - y0) / 2 = 0 := by rw [h, sub_self, zero_div]
    intro x
    rw [mk7_eta x, hform, c1, c2]
    funext t
    rcases t with i | i | u
    · fin_cases i <;> simp [mk7]
    · fin_cases i <;> simp [mk7]
    · simp [mk7]
  · right
    have c1 : (1 + y0) / 2 = 0 := by rw [h, add_neg_cancel, zero_div]
    have c2 : (1 - y0) / 2 = 1 := by rw [h, sub_neg_eq_add, one_add_one_eq_two, div_self h2]
    intro x
    rw [mk7_eta x, hform, c1, c2]
    funext t
    rcases t with i | i | u
    · fin_cases i <;> simp [mk7, Equiv.swap_apply_def]
    · fin_cases i <;> simp [mk7, Equiv.swap_apply_def]
    · simp [mk7, Equiv.swap_apply_def]

theorem spinAction_eq_one_of_fix_six (h2 : (2 : F) ≠ 0) (g : spinGroup (quadOdd 3 F))
    (a1 : spinAction (quadOdd 3 F) g (mk7 1 0 0 1 0 0 0) = mk7 1 0 0 1 0 0 0)
    (a2 : spinAction (quadOdd 3 F) g (mk7 0 0 0 0 0 0 1) = mk7 0 0 0 0 0 0 1)
    (a3 : spinAction (quadOdd 3 F) g (mk7 0 1 0 0 (-1) 0 0) = mk7 0 1 0 0 (-1) 0 0)
    (a4 : spinAction (quadOdd 3 F) g (mk7 0 0 1 0 0 (-1) 0) = mk7 0 0 1 0 0 (-1) 0)
    (a5 : spinAction (quadOdd 3 F) g (mk7 0 1 0 0 1 0 0) = mk7 0 1 0 0 1 0 0)
    (a6 : spinAction (quadOdd 3 F) g (mk7 0 0 1 0 0 1 0) = mk7 0 0 1 0 0 1 0) :
    spinAction (quadOdd 3 F) g = 1 := by
  have : Group.IsPerfect (spinGroup (quadOdd 3 F)) := isPerfect_spinGroup_quadOdd h2 (le_refl 3)
  rcases eq_one_or_swap_of_fix_six h2 g a1 a2 a3 a4 a5 a6 with h | h
  · exact LinearEquiv.ext fun x => by rw [h x]; rfl
  · exact absurd (CFSG.ClassicalInvolution.Asc77.T7H.det_spinAction_eq_one g)
      (det_swap_ne_one h2 _ h)

end Fix6

end CFSG.ClassicalInvolution.PhanB3.S
