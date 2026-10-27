module

public import CFSG.ClassicalInvolution.Phan.PhanS9A1Act

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

namespace A0

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem comp_eq_zero (D : KDat F K) (h2 : (2 : F) ≠ 0) {r s : F}
    (h : algebraMap F K r + D.θ * algebraMap F K s = 0) : r = 0 ∧ s = 0 := by
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of h2
  have hτ := congrArg D.τ h
  rw [map_add, map_mul, D.tau_alg, D.tau_alg, D.tau_theta, map_zero] at hτ
  have hr : algebraMap F K r = 0 := by
    have h' : (2 : K) * algebraMap F K r = 0 := by linear_combination h + hτ
    exact (mul_eq_zero.mp h').resolve_left h2K
  rw [hr, zero_add] at h
  have hs : algebraMap F K s = 0 := (mul_eq_zero.mp h).resolve_left (theta_ne D)
  exact ⟨(map_eq_zero_iff _ (algebraMap F K).injective).mp hr,
    (map_eq_zero_iff _ (algebraMap F K).injective).mp hs⟩

end A0

section Targets

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K) (h2 : (2 : F) ≠ 0)

theorem exists_rotSL0_of_fix_vXi (A : SL(2, F)) {c : K} (hc : c ≠ 0)
    (h : extK (La0 h2 A).toLinearMap (vXi D) = c • vXi D) :
    ∃ (a b : F) (hab : a ^ 2 + b ^ 2 = 1), A = rotSL0 a b hab := by
  have _hc := hc
  obtain ⟨p, q, r, s, hA⟩ := A0.exists_pqrs h2 A
  rw [A0.La0_vXi_pqrs D h2 A p q r s hA] at h
  have h1 := congrFun h (Sum.inl 1)
  have h1' : algebraMap F K r + D.θ * algebraMap F K s = 0 := by
    simpa [vXi, vE2, mk7] using h1
  obtain ⟨hr, hs⟩ := A0.comp_eq_zero D h2 h1'
  subst hr hs
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.2
  rw [hA, Matrix.det_fin_two_of] at hdet
  have hab : p ^ 2 + q ^ 2 = 1 := by linear_combination hdet
  refine ⟨p, q, hab, ?_⟩
  apply Subtype.ext
  rw [hA, rotSL0_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_rotSL0_of_mapsTo_P (A : SL(2, F))
    (h : ∀ s z : F, ∃ s' z' : F, La0 h2 A (mk7 s 0 0 s 0 0 z) = mk7 s' 0 0 s' 0 0 z') :
    ∃ (a b : F) (hab : a ^ 2 + b ^ 2 = 1), A = rotSL0 a b hab := by
  obtain ⟨s', z', hs⟩ := h 1 0
  have h1 := congrArg (fr0 h2).coords hs
  rw [La0, Frame.coords_La, A0.coords_P, A0.coords_P] at h1
  have hA : (A : Matrix (Fin 2) (Fin 2) F) = !![s', -z'; z', s'] := by
    rw [← h1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.2
  rw [hA, Matrix.det_fin_two_of] at hdet
  have hab : s' ^ 2 + (-z') ^ 2 = 1 := by linear_combination hdet
  refine ⟨s', -z', hab, ?_⟩
  apply Subtype.ext
  rw [hA, rotSL0_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Targets

end CFSG.ClassicalInvolution.PhanB3.S
