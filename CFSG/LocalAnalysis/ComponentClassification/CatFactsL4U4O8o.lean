module

public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitExtension
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit (extension)

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem reflect_reflect_of_polar_zero (Q : QuadraticForm K V) {u u' : V} (hu : Q u ≠ 0)
    (hu' : Q u' ≠ 0) (horth : polar Q u u' = 0) (x : V) :
    reflect Q u (reflect Q u' x) =
      x - (polar Q u' x / Q u') • u' - (polar Q u x / Q u) • u := by
  rw [reflect_apply hu, reflect_apply hu', polar_sub_right, polar_smul_right, horth, smul_zero,
    sub_zero]

variable (c₀ : K) (hc₀ : c₀ ≠ 0) (Q : QuadraticForm K V) (ξ : V ≃ₗ[K] (Fin 4 → extension c₀))
  (hpol : ∀ v u, ξ u 2 = 0 → ξ u 3 = 0 → polar Q v u = (ξ v 0 * ξ u 1 + ξ u 0 * ξ v 1).re)
  (hQu : ∀ u, ξ u 2 = 0 → ξ u 3 = 0 → Q u = (ξ u 0 * ξ u 1).re)

abbrev vu1 : V := ξ.symm ![⟨0, 1⟩, ⟨0, 1⟩, 0, 0]
abbrev vu2 : V := ξ.symm ![⟨0, 1⟩, ⟨0, -1⟩, 0, 0]
abbrev vw1 : V := ξ.symm ![⟨1, 1⟩, ⟨1, c₀⁻¹⟩, 0, 0]
abbrev vw2 : V := ξ.symm ![⟨1, -1⟩, ⟨-1, c₀⁻¹⟩, 0, 0]

include hQu in
theorem Q_vu1 : Q (vu1 c₀ ξ) = c₀ := by
  rw [hQu _ (by simp) (by simp)]
  simp

include hQu in
theorem Q_vu2 : Q (vu2 c₀ ξ) = -c₀ := by
  rw [hQu _ (by simp) (by simp)]
  simp

include hQu hc₀ in
theorem Q_vw1 : Q (vw1 c₀ ξ) = 2 := by
  rw [hQu _ (by simp) (by simp)]
  simp only [LinearEquiv.apply_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    QuadraticAlgebra.re_mul]
  field_simp
  ring

include hQu hc₀ in
theorem Q_vw2 : Q (vw2 c₀ ξ) = -2 := by
  rw [hQu _ (by simp) (by simp)]
  simp only [LinearEquiv.apply_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    QuadraticAlgebra.re_mul]
  field_simp
  ring

include hpol hQu hc₀ in
theorem reflect_u (v : V) :
    ξ (reflect Q (vu1 c₀ ξ) (reflect Q (vu2 c₀ ξ) v)) =
      ![star (ξ v 0), star (ξ v 1), ξ v 2, ξ v 3] := by
  have h1 := Q_vu1 c₀ Q ξ hQu
  have h2 := Q_vu2 c₀ Q ξ hQu
  have horth : polar Q (vu1 c₀ ξ) (vu2 c₀ ξ) = 0 := by
    rw [hpol _ _ (by simp) (by simp)]
    simp
  rw [reflect_reflect_of_polar_zero Q (by rw [h1]; exact hc₀)
    (by rw [h2]; exact neg_ne_zero.mpr hc₀) horth, polar_comm, polar_comm Q (vu1 c₀ ξ),
    hpol _ _ (by simp) (by simp),
    hpol _ _ (by simp) (by simp), h1, h2, map_sub, map_sub, map_smul, map_smul]
  funext i
  fin_cases i
  all_goals simp only [LinearEquiv.apply_symm_apply, Pi.sub_apply, Pi.smul_apply,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue]
  all_goals ext
  all_goals simp [QuadraticAlgebra.re_mul]
  all_goals field_simp
  all_goals ring

include hpol hQu hc₀ in
theorem reflect_w (h2K : (2 : K) ≠ 0) (v : V) :
    ξ (reflect Q (vw1 c₀ ξ) (reflect Q (vw2 c₀ ξ) v)) =
      ![⟨0, -1⟩ * ξ v 1, ⟨0, -c₀⁻¹⟩ * ξ v 0, ξ v 2, ξ v 3] := by
  have h1 := Q_vw1 c₀ hc₀ Q ξ hQu
  have h2 := Q_vw2 c₀ hc₀ Q ξ hQu
  have horth : polar Q (vw1 c₀ ξ) (vw2 c₀ ξ) = 0 := by
    rw [hpol _ _ (by simp) (by simp)]
    simp only [LinearEquiv.apply_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul]
    field_simp
    ring
  rw [reflect_reflect_of_polar_zero Q (by rw [h1]; exact h2K)
    (by rw [h2]; exact neg_ne_zero.mpr h2K) horth, polar_comm, polar_comm Q (vw1 c₀ ξ),
    hpol _ _ (by simp) (by simp),
    hpol _ _ (by simp) (by simp), h1, h2, map_sub, map_sub, map_smul, map_smul]
  funext i
  fin_cases i
  all_goals simp only [LinearEquiv.apply_symm_apply, Pi.sub_apply, Pi.smul_apply,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue]
  all_goals ext
  all_goals simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  all_goals field_simp
  all_goals ring

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
