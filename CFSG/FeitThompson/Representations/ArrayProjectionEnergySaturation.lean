module

public import CFSG.FeitThompson.Representations.ClassFunctionCauchySchwarzProjection
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CauchySchwarzProjection

open ComplexConjugate
open scoped ComplexOrder

theorem irr_eq_Irr (G : Type*) [Group G] : irr G = Irr G :=
  Set.ext fun _ => mem_irr.trans mem_Irr.symm

theorem span_irr_le_virtualChars (G : Type*) [Group G] :
    Submodule.span ℤ (irr G) ≤ virtualChars G :=
  Submodule.span_le.2 (by rw [irr_eq_Irr]; exact Irr_subset_virtualChars)

variable {G : Type*} [Fintype G]

theorem classFunInner_self_ofReal_re (f : G → ℂ) :
    (((classFunInner f f).re : ℝ) : ℂ) = classFunInner f f := by
  rw [classFunInner_self_re, ← classFunInner_self_eq_ofReal]

theorem classFunInner_self_re_nonneg (f : G → ℂ) : 0 ≤ (classFunInner f f).re := by
  rw [classFunInner_self_re]; positivity

theorem classFunInner_self_re_eq_zero {f : G → ℂ} : (classFunInner f f).re = 0 ↔ f = 0 := by
  rw [← classFunInner_self_eq_zero (f := f), ← classFunInner_self_ofReal_re f]
  simp

section Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {η : ι → G → ℂ}

theorem classFunInner_sum_smul_left
    (hη : ∀ k l, classFunInner (η k) (η l) = if k = l then 1 else 0) (c : ι → ℂ) (l : ι) :
    classFunInner (∑ k, c k • η k) (η l) = c l := by
  rw [classFunInner_sum_left, Finset.sum_eq_single_of_mem l (Finset.mem_univ l)]
  · rw [classFunInner_smul_left, hη l l, if_pos rfl, mul_one]
  · intro k _ hkl
    rw [classFunInner_smul_left, hη k l, if_neg hkl, mul_zero]

theorem classFunInner_sum_smul_self
    (hη : ∀ k l, classFunInner (η k) (η l) = if k = l then 1 else 0) (c : ι → ℂ) :
    classFunInner (∑ k, c k • η k) (∑ k, c k • η k) = ∑ k, c k * conj (c k) := by
  rw [classFunInner_sum_right]
  exact Finset.sum_congr rfl fun k _ => by
    rw [classFunInner_smul_right, classFunInner_sum_smul_left hη c k, mul_comm]

theorem classFunInner_self_eq_add_of_inner_eq
    (hη : ∀ k l, classFunInner (η k) (η l) = if k = l then 1 else 0) (f : G → ℂ) (c : ι → ℂ)
    (hc : ∀ k, classFunInner f (η k) = c k) :
    classFunInner f f = (∑ k, c k * conj (c k)) +
      classFunInner (f - ∑ k, c k • η k) (f - ∑ k, c k • η k) := by
  set X := ∑ k, c k • η k with hX
  have hYη : ∀ k, classFunInner (f - X) (η k) = 0 := fun k => by
    rw [classFunInner_sub_left, hc k, hX, classFunInner_sum_smul_left hη c k, sub_self]
  have hYX : classFunInner (f - X) X = 0 := by
    rw [hX, classFunInner_sum_right]
    exact Finset.sum_eq_zero fun k _ => by rw [classFunInner_smul_right, hYη k, mul_zero]
  have hXY : classFunInner X (f - X) = 0 := by
    rw [← classFunInner_conj_symm, hYX, map_zero]
  have hsum : X + (f - X) = f := add_sub_cancel _ _
  calc classFunInner f f
      = classFunInner (X + (f - X)) (X + (f - X)) := by rw [hsum]
    _ = classFunInner X X + classFunInner (f - X) (f - X) := by
        rw [classFunInner_add_left, classFunInner_add_right, classFunInner_add_right, hYX, hXY]
        ring
    _ = _ := by rw [classFunInner_sum_smul_self hη c]

end Family

variable [Group G]

theorem classFunInner_one_one : classFunInner (1 : G → ℂ) (1 : G → ℂ) = 1 := by
  have h : (Fintype.card G : ℂ) ≠ 0 := by simp
  simp [classFunInner_apply, Finset.card_univ, h]

theorem array_energy_saturation {m n : ℕ} [NeZero m] [NeZero n]
    {η : Fin m × Fin n → G → ℂ} {β z Γ : G → ℂ} {a : Fin m × Fin n → ℤ} {e : ℤ}
    (_hηmem : ∀ p, η p ∈ virtualChars G)
    (hη : ∀ p q, classFunInner (η p) (η q) = if p = q then 1 else 0)
    (_hη0 : η (0, 0) = 1)
    (_hβmem : β ∈ virtualChars G) (_hz : z ∈ classFun G) (_hΓ : Γ ∈ classFun G)
    (_he1 : 1 ≤ e) (hemn : e ≤ (m : ℤ) * n)
    (hβ : β = 1 + z + Γ)
    (hz0 : ∀ p, classFunInner z (η p) = 0)
    (hΓ0 : classFunInner Γ 1 = 0)
    (hΓnorm : classFunInner Γ Γ ≤ (e : ℂ) - 1)
    (ha : ∀ p, classFunInner β (η p) = (a p : ℂ))
    (hodd : ∀ p, Odd (a p)) :
    e = (m : ℤ) * n ∧ (∀ p, a p = 1 ∨ a p = -1) ∧
      Γ + 1 = ∑ p, (a p : ℂ) • η p := by
  classical
  have hcoeff : ∀ p, classFunInner (Γ + 1) (η p) = ((a p : ℤ) : ℂ) := fun p => by
    have hsub : Γ + (1 : G → ℂ) = β - z := by rw [hβ]; abel
    rw [hsub, classFunInner_sub_left, ha p, hz0 p, sub_zero]
  set X : G → ℂ := ∑ p, ((a p : ℤ) : ℂ) • η p with hX
  set R : G → ℂ := (Γ + 1) - X with hR
  have hpyth := classFunInner_self_eq_add_of_inner_eq hη (Γ + 1) (fun p => ((a p : ℤ) : ℂ)) hcoeff
  have h1Γ : classFunInner (1 : G → ℂ) Γ = 0 := by
    rw [← classFunInner_conj_symm, hΓ0, map_zero]
  have hone : classFunInner (Γ + 1) (Γ + (1 : G → ℂ)) = classFunInner Γ Γ + 1 := by
    rw [classFunInner_add_left, classFunInner_add_right, classFunInner_add_right, hΓ0, h1Γ,
      classFunInner_one_one]
    ring
  set T : ℤ := ∑ p, a p ^ 2 with hT
  have hsumsq : (∑ p, ((a p : ℤ) : ℂ) * conj (((a p : ℤ) : ℂ))) = (T : ℂ) := by
    rw [hT]
    push_cast
    exact Finset.sum_congr rfl fun p _ => by rw [map_intCast]; ring
  have hre : (classFunInner Γ Γ).re + 1 = (T : ℝ) + (classFunInner R R).re := by
    rw [hone, hsumsq, ← hR] at hpyth
    simpa using congrArg Complex.re hpyth
  have hΓre : (classFunInner Γ Γ).re ≤ (e : ℝ) - 1 := by
    simpa using (Complex.le_def.1 hΓnorm).1
  have hRre : 0 ≤ (classFunInner R R).re := classFunInner_self_re_nonneg R
  have hsq1 : ∀ p, 1 ≤ a p ^ 2 := by
    intro p
    have hp := hodd p
    have h0 : a p ≠ 0 := by
      intro h
      rw [h] at hp
      simp at hp
    nlinarith [sq_abs (a p), Int.one_le_abs h0]
  have hTge : (m : ℤ) * n ≤ T := by
    have := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin m × Fin n))) => hsq1 p)
    simpa [hT, Finset.card_univ] using this
  have hTgeR : ((m : ℝ) * n) ≤ (T : ℝ) := by exact_mod_cast hTge
  have hemnR : (e : ℝ) ≤ (m : ℝ) * n := by exact_mod_cast hemn
  have hR0 : (classFunInner R R).re = 0 := by linarith
  have heq : (e : ℝ) = (m : ℝ) * n := by linarith
  have hTeq : (T : ℝ) = (m : ℝ) * n := by linarith
  refine ⟨by exact_mod_cast heq, ?_, ?_⟩
  ·
    have hTZ : T = (Finset.univ : Finset (Fin m × Fin n)).card := by
      have : (T : ℝ) = ((Finset.univ : Finset (Fin m × Fin n)).card : ℝ) := by
        rw [hTeq]; simp
      exact_mod_cast this
    have hall := (Finset.sum_eq_sum_iff_of_le
      (fun p (_ : p ∈ (Finset.univ : Finset (Fin m × Fin n))) => hsq1 p)).1
      (by simpa [hT] using hTZ.symm)
    intro p
    have hp : a p ^ 2 = 1 := (hall p (Finset.mem_univ p)).symm
    have habs : |a p| = 1 := by nlinarith [sq_abs (a p), abs_nonneg (a p)]
    exact (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).1 habs
  ·
    have hR' : R = 0 := classFunInner_self_re_eq_zero.1 hR0
    rw [hR, sub_eq_zero] at hR'
    exact hR'

end CauchySchwarzProjection

end CFSG.FeitThompson
