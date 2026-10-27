module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyDef
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Floor

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

theorem eq_sign_of_odd {χ : Equiv.Perm (Fin 5) →* ℤˣ}
    (hχ : ∀ σ, Equiv.Perm.sign σ = -1 → χ σ = -1) : χ = Equiv.Perm.sign := by
  apply Equiv.Perm.eq_sign_of_surjective_hom
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, map_one χ⟩
  · exact ⟨Equiv.swap 0 1, hχ _ (Equiv.Perm.sign_swap (by decide))⟩

theorem dihChar_of_hom {χ : DihedralGroup 4 →* ℤˣ} (h1 : χ (DihedralGroup.r 1) = -1)
    (d : DihedralGroup 4) : χ d = dihChar (χ (DihedralGroup.sr 0)) d := by
  have hr : ∀ k : ZMod 4, χ (DihedralGroup.r k) = (-1) ^ k.val := by
    intro k
    have : (DihedralGroup.r k : DihedralGroup 4) = (DihedralGroup.r 1) ^ k.val := by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    rw [this, map_pow, h1]
  cases d with
  | r k => exact hr k
  | sr k =>
    have h2 : χ (DihedralGroup.sr k) = χ (DihedralGroup.sr 0) * (-1) ^ k.val := by
      have : (DihedralGroup.sr k : DihedralGroup 4) =
          DihedralGroup.sr 0 * DihedralGroup.r k := by simp
      rw [this, map_mul, hr k]
    exact h2.trans (dihChar_sr _ k).symm

end CFSG.EvenSporadicStandard.TwoHS
