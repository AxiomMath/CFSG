module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.Monster.SteinbergBQOddPrimeCongruenceTorsionFree

public section

namespace CFSG.StandardType

open Matrix

theorem int_matrix_eq_one_of_pow_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {X : Matrix ι ι ℤ} {k : ℕ} (hk : k ≠ 0) (hX : X ^ k = 1)
    (hmod : ∀ i j, (p : ℤ) ∣ (X - 1) i j) : X = 1 := by
  set f : ℤ →+* CFSG.Monster.ratLocal p := Int.castRingHom _ with hf
  set u : GL ι ℤ := Units.ofPowEqOne X k hX hk with hu
  have huX : (u : Matrix ι ι ℤ) = X := rfl
  have hfin : IsOfFinOrder (Matrix.GeneralLinearGroup.map f u) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨k, Nat.pos_of_ne_zero hk, by
      rw [← map_pow, hu, Units.pow_ofPowEqOne, map_one]⟩
  have hred : Matrix.GeneralLinearGroup.map (CFSG.Monster.ratLocalRed p)
      (Matrix.GeneralLinearGroup.map f u) = 1 := by
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, huX,
      ← RingHom.comp_apply, eq_intCast, Units.val_one]
    have h1 := hmod i j
    rw [Matrix.sub_apply, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub,
      sub_eq_zero] at h1
    rw [h1, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hg := (CFSG.Monster.odd_prime_congruence_torsion_free p hp2 ι).1 _ hred hfin
  ext i j
  have h2 := congrArg (fun v : GL ι (CFSG.Monster.ratLocal p) =>
    ((v : Matrix ι ι (CFSG.Monster.ratLocal p)) i j : ℚ)) hg
  simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one, huX, hf, eq_intCast] at h2
  rw [Matrix.one_apply] at h2 ⊢
  split_ifs at h2 ⊢ with hij
  · exact_mod_cast h2
  · exact_mod_cast h2

end CFSG.StandardType
