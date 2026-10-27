module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.LinearCombination

public section

open Matrix

namespace CFSG.GH74.GLS.IVK

variable {E : Type} [Field E]

private def sl2Up (x : E) : SpecialLinearGroup (Fin 2) E :=
  ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

private def sl2Lo (x : E) : SpecialLinearGroup (Fin 2) E :=
  ⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two]⟩

private theorem sl2Up_mulVec (x : E) (v : Fin 2 → E) :
    ((sl2Up x : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) *ᵥ v =
      ![v 0 + x * v 1, v 1] := by
  ext i
  fin_cases i <;> simp [sl2Up, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem sl2Lo_mulVec (x : E) (v : Fin 2 → E) :
    ((sl2Lo x : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) *ᵥ v =
      ![v 0, x * v 0 + v 1] := by
  ext i
  fin_cases i <;> simp [sl2Lo, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem vec_decomp (u : Fin 2 → E) : u = u 0 • ![1, 0] + u 1 • ![0, 1] := by
  ext i
  fin_cases i <;> simp

private theorem exists_ne_of_ne_one (σ : E ≃+* E) (hσ : σ ≠ 1) : ∃ x : E, σ x ≠ x := by
  by_contra h
  refine hσ (RingEquiv.ext fun x => ?_)
  by_contra hx
  exact h ⟨x, hx⟩

theorem sl2_invariant_bilinear_skew (h2 : (2 : E) ≠ 0)
    (F : (Fin 2 → E) →ₗ[E] (Fin 2 → E) →ₗ[E] E)
    (hF : ∀ g : SpecialLinearGroup (Fin 2) E, ∀ u v : Fin 2 → E,
      F ((g : Matrix (Fin 2) (Fin 2) E) *ᵥ u) ((g : Matrix (Fin 2) (Fin 2) E) *ᵥ v) = F u v) :
    ∀ u v : Fin 2 → E, F u v = - F v u := by
  have _ := h2
  obtain ⟨a, b, c, d, hexp⟩ : ∃ a b c d : E, ∀ u v : Fin 2 → E,
      F u v = u 0 * v 0 * a + u 0 * v 1 * b + u 1 * v 0 * c + u 1 * v 1 * d := by
    refine ⟨F ![1, 0] ![1, 0], F ![1, 0] ![0, 1], F ![0, 1] ![1, 0], F ![0, 1] ![0, 1],
      fun u v => ?_⟩
    conv_lhs => rw [vec_decomp u, vec_decomp v]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have ha : a = 0 := by
    have h := hF (sl2Up 1) ![1, 0] ![0, 1]
    simp only [sl2Up_mulVec, hexp, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    linear_combination h
  have hbc : b + c = 0 := by
    have h := hF (sl2Up 1) ![0, 1] ![0, 1]
    simp only [sl2Up_mulVec, hexp, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    linear_combination h - ha
  have hd : d = 0 := by
    have h := hF (sl2Lo 1) ![1, 0] ![0, 1]
    simp only [sl2Lo_mulVec, hexp, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    linear_combination h
  intro u v
  rw [hexp u v, hexp v u]
  linear_combination (2 * (u 0 * v 0)) * ha + (u 0 * v 1 + u 1 * v 0) * hbc +
    (2 * (u 1 * v 1)) * hd

theorem sl2_semilinear_commutant_zero (σ : E ≃+* E) (hσ : σ ≠ 1)
    (T : (Fin 2 → E) →+ (Fin 2 → E)) (hT : ∀ (a : E) (v : Fin 2 → E), T (a • v) = σ a • T v)
    (hc : ∀ g : SpecialLinearGroup (Fin 2) E, ∀ v : Fin 2 → E,
      T ((g : Matrix (Fin 2) (Fin 2) E) *ᵥ v) = (g : Matrix (Fin 2) (Fin 2) E) *ᵥ T v) :
    T = 0 := by
  obtain ⟨p, q, r, s, hexp⟩ : ∃ p q r s : E, ∀ v : Fin 2 → E,
      T v = ![σ (v 0) * p + σ (v 1) * r, σ (v 0) * q + σ (v 1) * s] := by
    refine ⟨T ![1, 0] 0, T ![1, 0] 1, T ![0, 1] 0, T ![0, 1] 1, fun v => ?_⟩
    conv_lhs => rw [vec_decomp v]
    rw [map_add, hT, hT]
    ext i
    fin_cases i <;> simp
  have hq : q = 0 := by
    have h := congrFun (hc (sl2Up 1) ![1, 0]) 0
    simp [sl2Up_mulVec, hexp] at h
    linear_combination h
  have hr : r = 0 := by
    have h := congrFun (hc (sl2Lo 1) ![1, 0]) 0
    simp [sl2Lo_mulVec, hexp] at h
    linear_combination h
  have hps : ∀ x : E, σ x * p = x * s := by
    intro x
    have h := congrFun (hc (sl2Up x) ![0, 1]) 0
    simp [sl2Up_mulVec, hexp] at h
    linear_combination h
  have hps1 : p = s := by simpa using hps 1
  have hp : p = 0 := by
    obtain ⟨x, hx⟩ := exists_ne_of_ne_one σ hσ
    have h3 : (σ x - x) * p = 0 := by linear_combination hps x - x * hps1
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hx)
  have hs : s = 0 := hps1 ▸ hp
  refine AddMonoidHom.ext fun v => ?_
  rw [hexp v, hp, hq, hr, hs]
  ext i
  fin_cases i <;> simp

theorem sl2_sesquilinear_invariant_zero (σ : E ≃+* E) (hσ : σ ≠ 1)
    (γ : (Fin 2 → E) → (Fin 2 → E) → E)
    (hadd₁ : ∀ u u' v, γ (u + u') v = γ u v + γ u' v)
    (hadd₂ : ∀ u v v', γ u (v + v') = γ u v + γ u v')
    (hs₁ : ∀ (a : E) u v, γ (a • u) v = σ a * γ u v)
    (hs₂ : ∀ (a : E) u v, γ u (a • v) = a * γ u v)
    (hinv : ∀ g : SpecialLinearGroup (Fin 2) E, ∀ u v : Fin 2 → E,
      γ ((g : Matrix (Fin 2) (Fin 2) E) *ᵥ u) ((g : Matrix (Fin 2) (Fin 2) E) *ᵥ v) = γ u v) :
    ∀ u v, γ u v = 0 := by
  obtain ⟨a, b, c, d, hexp⟩ : ∃ a b c d : E, ∀ u v : Fin 2 → E,
      γ u v = σ (u 0) * v 0 * a + σ (u 0) * v 1 * b + σ (u 1) * v 0 * c + σ (u 1) * v 1 * d := by
    refine ⟨γ ![1, 0] ![1, 0], γ ![1, 0] ![0, 1], γ ![0, 1] ![1, 0], γ ![0, 1] ![0, 1],
      fun u v => ?_⟩
    conv_lhs => rw [vec_decomp u, vec_decomp v]
    simp only [hadd₁, hadd₂, hs₁, hs₂]
    ring
  have ha : a = 0 := by
    have h := hinv (sl2Up 1) ![1, 0] ![0, 1]
    simp [sl2Up_mulVec, hexp] at h
    linear_combination h
  have hbc : b + c = 0 := by
    have h := hinv (sl2Up 1) ![0, 1] ![0, 1]
    simp [sl2Up_mulVec, hexp] at h
    linear_combination h - ha
  have hbx : ∀ x : E, σ x * b + x * c = 0 := by
    intro x
    have h := hinv (sl2Up x) ![0, 1] ![0, 1]
    simp [sl2Up_mulVec, hexp, ha] at h
    linear_combination h
  have hb : b = 0 := by
    obtain ⟨x, hx⟩ := exists_ne_of_ne_one σ hσ
    have h3 : (σ x - x) * b = 0 := by linear_combination hbx x - x * hbc
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hx)
  have hc0 : c = 0 := by linear_combination hbc - hb
  have hd : d = 0 := by
    have h := hinv (sl2Lo 1) ![1, 0] ![0, 1]
    simp [sl2Lo_mulVec, hexp] at h
    linear_combination h
  intro u v
  rw [hexp u v, ha, hb, hc0, hd]
  ring

theorem sl2_commutant_scalar (S : Matrix (Fin 2) (Fin 2) E)
    (hc : ∀ g : SpecialLinearGroup (Fin 2) E, S * (g : Matrix (Fin 2) (Fin 2) E) =
      (g : Matrix (Fin 2) (Fin 2) E) * S) : ∃ c : E, S = scalar (Fin 2) c := by
  obtain ⟨c, hc'⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct (M := S)
    fun t => (hc ⟨t.toMatrix, t.det⟩).symm
  exact ⟨c, hc'.symm⟩

end CFSG.GH74.GLS.IVK
