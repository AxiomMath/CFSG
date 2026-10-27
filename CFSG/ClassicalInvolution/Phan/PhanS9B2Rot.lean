module

public import CFSG.ClassicalInvolution.Phan.PhanS9B1Formula
public import CFSG.ClassicalInvolution.Phan.PhanS7Ctx

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

namespace HA1

section Vec

variable {K : Type} [Field K]

theorem add_mk7 (x0 x1 x2 y0 y1 y2 z x0' x1' x2' y0' y1' y2' z' : K) :
    mk7 x0 x1 x2 y0 y1 y2 z + mk7 x0' x1' x2' y0' y1' y2' z' =
      mk7 (x0 + x0') (x1 + x1') (x2 + x2') (y0 + y0') (y1 + y1') (y2 + y2') (z + z') := by
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · rfl

theorem smul_mk7 (c x0 x1 x2 y0 y1 y2 z : K) :
    c • mk7 x0 x1 x2 y0 y1 y2 z =
      mk7 (c * x0) (c * x1) (c * x2) (c * y0) (c * y1) (c * y2) (c * z) := by
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · rfl

omit [Field K] in
theorem mk7_eq_iff {x0 x1 x2 y0 y1 y2 z x0' x1' x2' y0' y1' y2' z' : K} :
    mk7 x0 x1 x2 y0 y1 y2 z = mk7 x0' x1' x2' y0' y1' y2' z' ↔
      x0 = x0' ∧ x1 = x1' ∧ x2 = x2' ∧ y0 = y0' ∧ y1 = y1' ∧ y2 = y2' ∧ z = z' := by
  refine ⟨fun h => ⟨congrFun h (.inl 0), congrFun h (.inl 1), congrFun h (.inl 2),
    congrFun h (.inr (.inl 0)), congrFun h (.inr (.inl 1)), congrFun h (.inr (.inl 2)),
    congrFun h (.inr (.inr ()))⟩, ?_⟩
  rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

end Vec

section Theta

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem two_ne_zero_K (h2 : (2 : F) ≠ 0) : (2 : K) ≠ 0 := by
  intro h
  exact h2 ((algebraMap F K).injective (by rw [map_ofNat, map_zero]; exact h))

theorem theta_ne_zero : D.θ ≠ 0 := by
  intro h
  have := D.theta_sq
  rw [h] at this
  simp at this

theorem eq_zero_of_add_theta (h2 : (2 : F) ≠ 0) {p q : F}
    (h : algebraMap F K p + algebraMap F K q * D.θ = 0) : p = 0 ∧ q = 0 := by
  have h' := congrArg D.τ h
  simp only [map_add, map_mul, D.tau_alg, D.tau_theta, map_zero] at h'
  have h1 : (2 : K) * (algebraMap F K q * D.θ) = 0 := by linear_combination h - h'
  have hq : algebraMap F K q = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left (two_ne_zero_K (K := K) h2))).resolve_right
      (theta_ne_zero D)
  have hp : algebraMap F K p = 0 := by simpa [hq] using h
  exact ⟨(map_eq_zero_iff _ (algebraMap F K).injective).mp hp,
    (map_eq_zero_iff _ (algebraMap F K).injective).mp hq⟩

end Theta

section Eval

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K) (h2 : (2 : F) ≠ 0)

theorem add_vE23 (α β : K) :
    α • vE2 D + β • vE3 D =
      mk7 0 (α + β) (D.θ * (β - α)) 0 (β - α) (D.θ * (α + β)) 0 := by
  rw [vE2, vE3, smul_mk7, smul_mk7, add_mk7, mk7_eq_iff]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring⟩

theorem extK_La1_vE2 (A : SL(2, F)) :
    extK (La1 h2 A).toLinearMap (vE2 D) =
      mk7 0 (algebraMap F K (A 0 0) - 2 * algebraMap F K (A 0 1) * D.θ)
        (D.θ * (-algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2)) 0
        (-algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2)
        (D.θ * (algebraMap F K (A 0 0) - 2 * algebraMap F K (A 0 1) * D.θ)) 0 := by
  have hθ := D.theta_sq
  rw [vE2, extK_La1_mk7, mk7_eq_iff]
  refine ⟨by ring, by ring, ?_, by ring, by ring, ?_, by ring⟩
  · linear_combination (algebraMap F K (A 1 0) / 2) * hθ
  · linear_combination (2 * algebraMap F K (A 0 1)) * hθ

theorem extK_La1_vE3 (A : SL(2, F)) :
    extK (La1 h2 A).toLinearMap (vE3 D) =
      mk7 0 (algebraMap F K (A 0 0) + 2 * algebraMap F K (A 0 1) * D.θ)
        (D.θ * (algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2)) 0
        (algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2)
        (D.θ * (algebraMap F K (A 0 0) + 2 * algebraMap F K (A 0 1) * D.θ)) 0 := by
  have hθ := D.theta_sq
  rw [vE3, extK_La1_mk7, mk7_eq_iff]
  refine ⟨by ring, by ring, ?_, by ring, by ring, ?_, by ring⟩
  · linear_combination (algebraMap F K (A 1 0) / 2) * hθ
  · linear_combination (-(2 * algebraMap F K (A 0 1))) * hθ

end Eval

end HA1

section Main

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K) (h2 : (2 : F) ≠ 0)

theorem La1_fix_vXi (A : SL(2, F)) : extK (La1 h2 A).toLinearMap (vXi D) = vXi D := by
  rw [vXi, extK_La1_mk7]
  simp

theorem La1_mem_l23 (A : SL(2, F)) : ∃ a b c d : K,
    extK (La1 h2 A).toLinearMap (vE2 D) = a • vE2 D + b • vE3 D ∧
    extK (La1 h2 A).toLinearMap (vE3 D) = c • vE2 D + d • vE3 D := by
  have h2K := HA1.two_ne_zero_K (K := K) h2
  have hi : 2 * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2K
  refine ⟨(2 : K)⁻¹ * ((algebraMap F K (A 0 0) - 2 * algebraMap F K (A 0 1) * D.θ) -
      (-algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2)),
    (2 : K)⁻¹ * ((algebraMap F K (A 0 0) - 2 * algebraMap F K (A 0 1) * D.θ) +
      (-algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2)),
    (2 : K)⁻¹ * ((algebraMap F K (A 0 0) + 2 * algebraMap F K (A 0 1) * D.θ) -
      (algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2)),
    (2 : K)⁻¹ * ((algebraMap F K (A 0 0) + 2 * algebraMap F K (A 0 1) * D.θ) +
      (algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2)), ?_, ?_⟩
  · rw [HA1.extK_La1_vE2, HA1.add_vE23, HA1.mk7_eq_iff]
    refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, rfl⟩
    · linear_combination (-(algebraMap F K (A 0 0) - 2 * algebraMap F K (A 0 1) * D.θ)) * hi
    · congr 1
      linear_combination (-(-algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2)) * hi
    · linear_combination (-(-algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2)) * hi
    · congr 1
      linear_combination (-(algebraMap F K (A 0 0) - 2 * algebraMap F K (A 0 1) * D.θ)) * hi
  · rw [HA1.extK_La1_vE3, HA1.add_vE23, HA1.mk7_eq_iff]
    refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, rfl⟩
    · linear_combination (-(algebraMap F K (A 0 0) + 2 * algebraMap F K (A 0 1) * D.θ)) * hi
    · congr 1
      linear_combination (-(algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2)) * hi
    · linear_combination (-(algebraMap F K (A 1 1) - algebraMap F K (A 1 0) * D.θ / 2)) * hi
    · congr 1
      linear_combination (-(algebraMap F K (A 0 0) + 2 * algebraMap F K (A 0 1) * D.θ)) * hi

theorem La1_rotSL1_vE2 (a b : F) (h : a ^ 2 + 4 * b ^ 2 = 1) :
    extK (La1 h2 (rotSL1 a b h)).toLinearMap (vE2 D) =
      (algebraMap F K a - 2 * algebraMap F K b * D.θ) • vE2 D := by
  have h2K := HA1.two_ne_zero_K (K := K) h2
  have hi : 2 * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2K
  rw [HA1.extK_La1_vE2, vE2, HA1.smul_mk7, HA1.mk7_eq_iff]
  have e00 : (rotSL1 a b h : Matrix (Fin 2) (Fin 2) F) 0 0 = a := rfl
  have e01 : (rotSL1 a b h : Matrix (Fin 2) (Fin 2) F) 0 1 = b := rfl
  have e10 : (rotSL1 a b h : Matrix (Fin 2) (Fin 2) F) 1 0 = -(4 * b) := rfl
  have e11 : (rotSL1 a b h : Matrix (Fin 2) (Fin 2) F) 1 1 = a := rfl
  simp only [e00, e01, e10, e11, map_neg, map_mul, map_ofNat]
  refine ⟨by ring, by ring, ?_, by ring, ?_, by ring, by ring⟩
  · linear_combination (2 * algebraMap F K b * D.θ ^ 2) * hi
  · linear_combination (2 * algebraMap F K b * D.θ) * hi

theorem La1_rotSL1_vE3 (a b : F) (h : a ^ 2 + 4 * b ^ 2 = 1) :
    extK (La1 h2 (rotSL1 a b h)).toLinearMap (vE3 D) =
      (algebraMap F K a + 2 * algebraMap F K b * D.θ) • vE3 D := by
  have h2K := HA1.two_ne_zero_K (K := K) h2
  have hi : 2 * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2K
  rw [HA1.extK_La1_vE3, vE3, HA1.smul_mk7, HA1.mk7_eq_iff]
  have e00 : (rotSL1 a b h : Matrix (Fin 2) (Fin 2) F) 0 0 = a := rfl
  have e01 : (rotSL1 a b h : Matrix (Fin 2) (Fin 2) F) 0 1 = b := rfl
  have e10 : (rotSL1 a b h : Matrix (Fin 2) (Fin 2) F) 1 0 = -(4 * b) := rfl
  have e11 : (rotSL1 a b h : Matrix (Fin 2) (Fin 2) F) 1 1 = a := rfl
  simp only [e00, e01, e10, e11, map_neg, map_mul, map_ofNat]
  refine ⟨by ring, by ring, ?_, by ring, ?_, by ring, by ring⟩
  · linear_combination (2 * algebraMap F K b * D.θ ^ 2) * hi
  · linear_combination (2 * algebraMap F K b * D.θ) * hi

theorem exists_rotSL1_of_fix_vE2 (A : SL(2, F)) {c : K} (hc : c ≠ 0)
    (h : extK (La1 h2 A).toLinearMap (vE2 D) = c • vE2 D) :
    ∃ (a b : F) (hab : a ^ 2 + 4 * b ^ 2 = 1), A = rotSL1 a b hab := by
  have _ := hc
  rw [HA1.extK_La1_vE2, vE2, HA1.smul_mk7, HA1.mk7_eq_iff] at h
  obtain ⟨-, h1, -, -, h3, -, -⟩ := h
  have key : algebraMap F K (A 0 0 - A 1 1) +
      algebraMap F K (-(2 * A 0 1) - A 1 0 / 2) * D.θ = 0 := by
    simp only [map_sub, map_neg, map_mul, map_div₀, map_ofNat]
    linear_combination h1 + h3
  obtain ⟨e1, e2⟩ := HA1.eq_zero_of_add_theta D h2 key
  have e1' : A 1 1 = A 0 0 := (sub_eq_zero.mp e1).symm
  have e2' : A 1 0 = -(4 * A 0 1) := by
    field_simp at e2
    linear_combination -e2
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.2
    rwa [Matrix.det_fin_two] at this
  refine ⟨A 0 0, A 0 1, ?_, ?_⟩
  · rw [e1', e2'] at hdet
    linear_combination hdet
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotSL1_apply, e1', e2']

theorem exists_rotSL1_of_mapsTo_Pp (A : SL(2, F))
    (h : ∀ a b : F, ∃ a' b' : F, La1 h2 A (mk7 0 a b 0 (-a) (-b) 0) = mk7 0 a' b' 0 (-a') (-b') 0) :
    ∃ (a b : F) (hab : a ^ 2 + 4 * b ^ 2 = 1), A = rotSL1 a b hab := by
  obtain ⟨a', b', hab⟩ := h 1 0
  rw [La1_mk7, HA1.mk7_eq_iff] at hab
  obtain ⟨-, h1, h2', -, h3, h4, -⟩ := hab
  have e1' : A 1 1 = A 0 0 := by linear_combination -h3 - h1
  have e2' : A 1 0 = -(4 * A 0 1) := by
    field_simp at h2' h4
    linear_combination h2' + 2 * h4
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.2
    rwa [Matrix.det_fin_two] at this
  refine ⟨A 0 0, A 0 1, ?_, ?_⟩
  · rw [e1', e2'] at hdet
    linear_combination hdet
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotSL1_apply, e1', e2']

end Main

end CFSG.ClassicalInvolution.PhanB3.S
