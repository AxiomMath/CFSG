module

public import CFSG.GH74.GLS.IVK.L2.TorusCentralizer

public section

namespace CFSG.GH74.GLS.IVK.L2Torus

open Matrix CFSG.Semidihedral.MatrixTorus CFSG.Semidihedral.MatrixCoverData
  CFSG.Semidihedral.OddFieldSL2

variable {F : Type*} [Field F]

theorem exists_commute_J_det [Finite F] (hF : ringChar F ≠ 2) (d : Fˣ) :
    ∃ c : GL2 F, c * J F 1 = J F 1 * c ∧ GeneralLinearGroup.det c = d := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨a, b, hab⟩ : ∃ a b : F, a ^ 2 + b ^ 2 = (d : F) := by
    have hdeg : (Polynomial.X ^ 2 : Polynomial F).degree = 2 := by
      rw [Polynomial.degree_X_pow]
      rfl
    obtain ⟨a, b, h⟩ := FiniteField.exists_root_sum_quadratic
      (f := (Polynomial.X ^ 2 : Polynomial F)) (g := (Polynomial.X ^ 2 - Polynomial.C (d : F)))
      hdeg (by rw [Polynomial.degree_sub_C (by rw [hdeg]; norm_num), hdeg])
      (FiniteField.odd_card_of_char_ne_two hF)
    refine ⟨a, b, ?_⟩
    simp at h
    linear_combination h
  have hdet : (!![a, -b; b, a] : Matrix (Fin 2) (Fin 2) F).det = d := by
    rw [Matrix.det_fin_two_of]
    linear_combination hab
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ (by rw [hdet]; exact d.ne_zero), ?_, ?_⟩
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [J_matrix, Matrix.mul_apply, Fin.sum_univ_two]
  · apply Units.ext
    simp [hdet]

theorem exists_sl_conj_J [Finite F] (hF : ringChar F ≠ 2) (h2 : (2 : F) ≠ 0) (x : SL F) (hx : x * x = minusIdentity F) :
    ∃ s : SL F, SpecialLinearGroup.toGL x =
      SpecialLinearGroup.toGL s * J F 1 * (SpecialLinearGroup.toGL s)⁻¹ := by
  obtain ⟨P, hP⟩ := exists_conj_J h2 x hx
  obtain ⟨c, hc, hdet⟩ := exists_commute_J_det hF (GeneralLinearGroup.det P)⁻¹
  have hQ : GeneralLinearGroup.det (P * c) = 1 := by
    rw [map_mul, hdet]
    simp
  have hmem : P * c ∈ (GeneralLinearGroup.det : GL2 F →* Fˣ).ker := hQ
  let s : SL F := (SpecialLinearGroup.toGLKerEquiv (n := Fin 2) (R := F)).symm ⟨P * c, hmem⟩
  have hs : SpecialLinearGroup.toGL s = P * c := by
    have := (SpecialLinearGroup.toGLKerEquiv (n := Fin 2) (R := F)).apply_symm_apply ⟨P * c, hmem⟩
    exact congrArg Subtype.val this
  refine ⟨s, ?_⟩
  rw [hs, hP]
  have hcJ : c * J F 1 * c⁻¹ = J F 1 := by
    rw [hc]
    group
  calc P * J F 1 * P⁻¹ = P * (c * J F 1 * c⁻¹) * P⁻¹ := by rw [hcJ]
    _ = P * c * J F 1 * (P * c)⁻¹ := by group

theorem exists_sl_conj_of_sq_eq_neg_one [Finite F] (hF : ringChar F ≠ 2) (h2 : (2 : F) ≠ 0) (x y : SL F)
    (hx : x * x = minusIdentity F) (hy : y * y = minusIdentity F) :
    ∃ g : SL F, g * x * g⁻¹ = y := by
  obtain ⟨sx, hsx⟩ := exists_sl_conj_J hF h2 x hx
  obtain ⟨sy, hsy⟩ := exists_sl_conj_J hF h2 y hy
  refine ⟨sy * sx⁻¹, ?_⟩
  apply SpecialLinearGroup.toGL_injective
  simp only [map_mul, map_inv]
  rw [hsx, hsy]
  group

end CFSG.GH74.GLS.IVK.L2Torus
