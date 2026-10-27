module

public import CFSG.LocalAnalysis.ComponentInitial.LinearMonomial
public import Mathlib.FieldTheory.IsAlgClosed.Basic

public section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open Matrix CFSG.LocalAnalysis.ComponentInitial

section General

variable {ι : Type*} [Fintype ι] {G : Type*} [CommGroup G]

@[expose] def monoHom (A : Matrix ι ι ℤ) : (ι → G) →* (ι → G) where
  toFun t i := ∏ j, t j ^ A i j
  map_one' := by
    ext i
    simp
  map_mul' s t := by
    ext i
    simp [mul_zpow, Finset.prod_mul_distrib]

@[simp] theorem monoHom_apply (A : Matrix ι ι ℤ) (t : ι → G) (i : ι) :
    monoHom A t i = ∏ j, t j ^ A i j := rfl

theorem monoHom_monoHom (A B : Matrix ι ι ℤ) (t : ι → G) :
    monoHom A (monoHom B t) = monoHom (A * B) t := by
  ext i
  simp only [monoHom_apply, Matrix.mul_apply]
  have h1 : ∀ j, (∏ k, t k ^ B j k) ^ A i j = ∏ k, t k ^ (B j k * A i j) := fun j => by
    rw [← Finset.prod_zpow]
    exact Finset.prod_congr rfl fun k _ => by rw [← zpow_mul]
  simp only [h1]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_finsetSum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_unit_zpow_eq {L : Type*} [Field L] [IsAlgClosed L] (s : Lˣ) {d : ℤ} (hd : d ≠ 0) :
    ∃ w : Lˣ, w ^ d = s := by
  have hpos : 0 < d.natAbs := Int.natAbs_pos.mpr hd
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (s : L) hpos
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hz
    exact s.ne_zero hz.symm
  set u : Lˣ := Units.mk0 z hz0
  have hu : u ^ d.natAbs = s := Units.ext (by simpa [u] using hz)
  rcases Int.natAbs_eq d with h | h
  · refine ⟨u, ?_⟩
    have : u ^ d = u ^ d.natAbs := by
      conv_lhs => rw [h]
      rw [zpow_natCast]
    rw [this, hu]
  · refine ⟨u⁻¹, ?_⟩
    have : (u⁻¹) ^ d = u ^ d.natAbs := by
      conv_lhs => rw [h]
      rw [zpow_neg, zpow_natCast, inv_pow, inv_inv]
    rw [this, hu]

theorem monoHom_surjective_of_det_ne_zero {L : Type*} [Field L] [IsAlgClosed L]
    (A : Matrix ι ι ℤ) [DecidableEq ι] (hA : A.det ≠ 0) :
    Function.Surjective (monoHom (G := Lˣ) A) := by
  intro s
  choose w hw using fun i => exists_unit_zpow_eq (s i) hA
  refine ⟨monoHom (A.adjugate) w, ?_⟩
  rw [monoHom_monoHom, Matrix.mul_adjugate]
  ext i
  simp only [monoHom_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [Finset.prod_eq_single i]
  · simp [hw i]
  · intro j _ hji
    simp [hji.symm]
  · intro h
    exact absurd (Finset.mem_univ i) h

end General

theorem monoHom_eq_monomialHom {G : Type*} [CommGroup G] {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) :
    (monoHom A : (Fin r → G) →* (Fin r → G)) = monomialHom A := rfl

end CFSG.HardMathSupport.Lang.TwE6Step3
