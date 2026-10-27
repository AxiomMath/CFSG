module

public import CFSG.ClassicalInvolution.Phan.PhanS9A0Frame

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

namespace A0

section Formulas

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem La0_vXi_pqrs (D : KDat F K) (h2 : (2 : F) ≠ 0) (A : SL(2, F)) (p q r s : F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) = !![p + r, q + s; s - q, p - r]) :
    extK (La0 h2 A).toLinearMap (vXi D) =
      (algebraMap F K p + D.θ * algebraMap F K q) • vXi D +
        (algebraMap F K r + D.θ * algebraMap F K s) • vE2 D := by
  have key : ((A : Matrix (Fin 2) (Fin 2) F).map (algebraMap F K)) *
      (!![1, -D.θ; D.θ, 1] : Matrix (Fin 2) (Fin 2) K) =
      (algebraMap F K p + D.θ * algebraMap F K q) •
        (!![1, -D.θ; D.θ, 1] : Matrix (Fin 2) (Fin 2) K) +
      (algebraMap F K r + D.θ * algebraMap F K s) •
        (!![1, -D.θ; -D.θ, -1] : Matrix (Fin 2) (Fin 2) K) := by
    rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · ring
    · linear_combination (algebraMap F K q + algebraMap F K s) * D.theta_sq
    · linear_combination (algebraMap F K s - algebraMap F K q) * D.theta_sq
    · ring
  rw [vXi_eq_iK D h2, vE2_eq_iK D h2, extK_La0_iK, key, map_add, map_smul, map_smul]

theorem La0_vE2_pqrs (D : KDat F K) (h2 : (2 : F) ≠ 0) (A : SL(2, F)) (p q r s : F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) = !![p + r, q + s; s - q, p - r]) :
    extK (La0 h2 A).toLinearMap (vE2 D) =
      (algebraMap F K r - D.θ * algebraMap F K s) • vXi D +
        (algebraMap F K p - D.θ * algebraMap F K q) • vE2 D := by
  have key : ((A : Matrix (Fin 2) (Fin 2) F).map (algebraMap F K)) *
      (!![1, -D.θ; -D.θ, -1] : Matrix (Fin 2) (Fin 2) K) =
      (algebraMap F K r - D.θ * algebraMap F K s) •
        (!![1, -D.θ; D.θ, 1] : Matrix (Fin 2) (Fin 2) K) +
      (algebraMap F K p - D.θ * algebraMap F K q) •
        (!![1, -D.θ; -D.θ, -1] : Matrix (Fin 2) (Fin 2) K) := by
    rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · ring
    · linear_combination (-(algebraMap F K q + algebraMap F K s)) * D.theta_sq
    · linear_combination (algebraMap F K s - algebraMap F K q) * D.theta_sq
    · ring
  rw [vXi_eq_iK D h2, vE2_eq_iK D h2, extK_La0_iK, key, map_add, map_smul, map_smul]

theorem exists_pqrs (h2 : (2 : F) ≠ 0) (A : SL(2, F)) :
    ∃ p q r s : F, (A : Matrix (Fin 2) (Fin 2) F) = !![p + r, q + s; s - q, p - r] := by
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : F, (A : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  refine ⟨(a + d) / 2, (b - c) / 2, (a - d) / 2, (b + c) / 2, ?_⟩
  have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have e1 : (a + d) / 2 + (a - d) / 2 = a := by linear_combination a * h
  have e2 : (b - c) / 2 + (b + c) / 2 = b := by linear_combination b * h
  have e3 : (b + c) / 2 - (b - c) / 2 = c := by linear_combination c * h
  have e4 : (a + d) / 2 - (a - d) / 2 = d := by linear_combination d * h
  rw [hM, e1, e2, e3, e4]

end Formulas

end A0

section Targets

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K) (h2 : (2 : F) ≠ 0)

theorem La0_fix_vE3 (A : SL(2, F)) : extK (La0 h2 A).toLinearMap (vE3 D) = vE3 D := by
  have h1 : (La0 h2 A).toLinearMap (mk7 (0 : F) 1 0 0 1 0 0) = mk7 0 1 0 0 1 0 0 :=
    Frame.La_apply_of_coords_eq_zero _ _ (A0.coords_perp₁ h2)
  have h3 : (La0 h2 A).toLinearMap (mk7 (0 : F) 0 1 0 0 1 0) = mk7 0 0 1 0 0 1 0 :=
    Frame.La_apply_of_coords_eq_zero _ _ (A0.coords_perp₂ h2)
  rw [A0.vE3_eq_emb D, map_add, map_smul, extK_emb, extK_emb, h1, h3]

theorem La0_mem_l0 (A : SL(2, F)) : ∃ a b c d : K,
    extK (La0 h2 A).toLinearMap (vXi D) = a • vXi D + b • vE2 D ∧
    extK (La0 h2 A).toLinearMap (vE2 D) = c • vXi D + d • vE2 D := by
  obtain ⟨p, q, r, s, hA⟩ := A0.exists_pqrs h2 A
  exact ⟨_, _, _, _, A0.La0_vXi_pqrs D h2 A p q r s hA, A0.La0_vE2_pqrs D h2 A p q r s hA⟩

theorem La0_rotSL0_vXi (a b : F) (h : a ^ 2 + b ^ 2 = 1) :
    extK (La0 h2 (rotSL0 a b h)).toLinearMap (vXi D) =
      (algebraMap F K a + algebraMap F K b * D.θ) • vXi D := by
  have hA : ((rotSL0 a b h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![a + 0, b + 0; 0 - b, a - 0] := by
    rw [rotSL0_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [A0.La0_vXi_pqrs D h2 _ a b 0 0 hA]
  simp [mul_comm]

theorem La0_rotSL0_vE2 (a b : F) (h : a ^ 2 + b ^ 2 = 1) :
    extK (La0 h2 (rotSL0 a b h)).toLinearMap (vE2 D) =
      (algebraMap F K a - algebraMap F K b * D.θ) • vE2 D := by
  have hA : ((rotSL0 a b h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![a + 0, b + 0; 0 - b, a - 0] := by
    rw [rotSL0_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [A0.La0_vE2_pqrs D h2 _ a b 0 0 hA]
  simp [mul_comm]

end Targets

end CFSG.ClassicalInvolution.PhanB3.S
