module

public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.GF2Type.Smith1980Orth.W4Sigma

open CFSG.GroupTheory.GLnTwoSplitting

theorem card_linearEquiv_eq_prod {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {n : ℕ} (hn : Module.finrank (ZMod 2) V = n) :
    Nat.card (V ≃ₗ[ZMod 2] V) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  classical
  let b : Module.Basis (Fin n) (ZMod 2) V := Module.finBasisOfFinrankEq (ZMod 2) V hn
  let e : GL (Fin n) (ZMod 2) ≃* (V ≃ₗ[ZMod 2] V) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V)
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field, ZMod.card]

theorem card_linearEquiv_of_finrank_eq_six {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    [FiniteDimensional (ZMod 2) A] (h6 : Module.finrank (ZMod 2) A = 6) :
    Nat.card (A ≃ₗ[ZMod 2] A) = 20158709760 := by
  rw [card_linearEquiv_eq_prod h6]
  simp [Fin.prod_univ_succ]

theorem card_linearEquiv_of_finrank_eq_five {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (h5 : Module.finrank (ZMod 2) V = 5) :
    Nat.card (V ≃ₗ[ZMod 2] V) = 9999360 := by
  rw [card_linearEquiv_eq_prod h5]
  simp [Fin.prod_univ_succ]

theorem not_dvd_card_of_finrank_eq_six {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    [FiniteDimensional (ZMod 2) A] (h6 : Module.finrank (ZMod 2) A = 6)
    (H : Subgroup (A ≃ₗ[ZMod 2] A)) : ¬ 47 ∣ Nat.card H := by
  intro h
  have h' := h.trans (Subgroup.card_subgroup_dvd_card H)
  rw [card_linearEquiv_of_finrank_eq_six h6] at h'
  revert h'
  norm_num

theorem eq_top_of_transitive_of_transvection_mem {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hT : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ h ∈ H, h v = w) {z : V} (hz : z ≠ 0)
    (htv : ∀ (f : Module.Dual (ZMod 2) V) (hf : f z = 0), LinearEquiv.transvection hf ∈ H) :
    H = ⊤ := by
  rw [eq_top_iff, ← closure_transvections_eq_top (E := V), Subgroup.closure_le]
  rintro _ ⟨f, d, hfd, rfl⟩
  by_cases hd : d = 0
  · subst hd
    rw [transvection_eq_one hfd]
    exact one_mem H
  · obtain ⟨h, hhH, hhz⟩ := hT z d hz hd
    have hfh : (f ∘ₗ (h : V →ₗ[ZMod 2] V)) z = 0 := by
      rw [LinearMap.comp_apply]
      exact (congrArg f hhz).trans hfd
    have hconj : LinearEquiv.transvection hfd =
        h * LinearEquiv.transvection hfh * h⁻¹ := by
      ext x
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, transvection_apply, transvection_apply]
      change _ = h (h.symm x + _)
      rw [map_add, map_smul, hhz, LinearEquiv.apply_symm_apply]
      simp
    rw [hconj]
    exact mul_mem (mul_mem hhH (htv _ hfh)) (inv_mem hhH)

theorem false_of_transitive_of_transvection_mem {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (h5 : Module.finrank (ZMod 2) V = 5)
    (H : Subgroup (V ≃ₗ[ZMod 2] V)) (hT : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ h ∈ H, h v = w)
    {z : V} (hz : z ≠ 0)
    (htv : ∀ (f : Module.Dual (ZMod 2) V) (hf : f z = 0), LinearEquiv.transvection hf ∈ H)
    (hcard : Nat.card H < 9999360) : False := by
  have hH := eq_top_of_transitive_of_transvection_mem H hT hz htv
  rw [hH, Subgroup.card_top, card_linearEquiv_of_finrank_eq_five h5] at hcard
  norm_num at hcard

end CFSG.GF2Type.Smith1980Orth.W4Sigma
