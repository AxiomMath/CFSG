module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionCoordinateEquiv

public section

namespace CFSG.GH74.E2

open Subgroup
open scoped commutatorElement

namespace Q8

variable {X : Type*} [Group X]

theorem pow_mod_four {x : X} (hx : x ^ 4 = 1) (n : ℕ) : x ^ (n % 4) = x ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, hx, one_pow, mul_one]

@[expose] noncomputable def coordHom (x : X) (hx : x ^ 4 = 1) : Multiplicative (ZMod 4) →* X where
  toFun k := x ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    change x ^ (Multiplicative.toAdd a + Multiplicative.toAdd b).val =
      x ^ (Multiplicative.toAdd a).val * x ^ (Multiplicative.toAdd b).val
    rw [ZMod.val_add, pow_mod_four hx, pow_add]

theorem coordHom_apply (x : X) (hx : x ^ 4 = 1) (k : ZMod 4) :
    coordHom x hx (Multiplicative.ofAdd k) = x ^ k.val := rfl

theorem quaternion_iso [Finite X] {x y : X} (hcard : Nat.card X = 8)
    (hx1 : x * x ≠ 1) (hx4 : x * x * (x * x) = 1) (hyy : y * y = x * x) (hxy : ⁅x, y⁆ = x * x) :
    Nonempty (QuaternionGroup 2 ≃* X) := by
  have hx4' : x ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    exact hx4
  have hyx : y * x * y⁻¹ = x⁻¹ := by
    have h1 : x * y * x⁻¹ * y⁻¹ = x * x := by
      rw [← commutatorElement_def]
      exact hxy
    have h2 : y * x⁻¹ * y⁻¹ = x := by
      calc y * x⁻¹ * y⁻¹ = x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group
        _ = x⁻¹ * (x * x) := by rw [h1]
        _ = x := by group
    calc y * x * y⁻¹ = (y * x⁻¹ * y⁻¹)⁻¹ := by group
      _ = x⁻¹ := by rw [h2]
  have hinv : ∀ n : ℕ, y * x ^ n * y⁻¹ = (x ^ n)⁻¹ := by
    intro n
    calc y * x ^ n * y⁻¹ = (y * x * y⁻¹) ^ n := by
          induction n with
          | zero => group
          | succ n ih =>
            calc y * x ^ (n + 1) * y⁻¹ = (y * x ^ n * y⁻¹) * (y * x * y⁻¹) := by group
              _ = (y * x * y⁻¹) ^ n * (y * x * y⁻¹) := by rw [ih]
              _ = (y * x * y⁻¹) ^ (n + 1) := by rw [pow_succ]
      _ = (x ^ n)⁻¹ := by rw [hyx, inv_pow]
  have hinj : Function.Injective (coordHom x hx4') := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : x ^ (Multiplicative.toAdd k).val = 1 := hk
    have hlt := ZMod.val_lt (Multiplicative.toAdd k)
    have hcases : (Multiplicative.toAdd k).val = 0 ∨ (Multiplicative.toAdd k).val = 1 ∨
        (Multiplicative.toAdd k).val = 2 ∨ (Multiplicative.toAdd k).val = 3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · have h00 : Multiplicative.toAdd k = 0 := (ZMod.val_eq_zero _).1 h0
      exact toAdd_eq_zero.1 h00
    · exfalso
      rw [h1, pow_one] at hk'
      apply hx1
      rw [hk', mul_one]
    · exfalso
      rw [h2, pow_two] at hk'
      exact hx1 hk'
    · exfalso
      rw [h3] at hk'
      apply hx1
      have h5 : x = x ^ 4 * (x ^ 3)⁻¹ := by group
      rw [hk', hx4', inv_one, mul_one] at h5
      rw [h5, mul_one]
  have hrange : Nat.card (coordHom x hx4').range = 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    simp
  have hindex : (coordHom x hx4').range.index = 2 := by
    have h1 := (coordHom x hx4').range.card_mul_index
    rw [hrange, hcard] at h1
    omega
  have houtside : y ∉ (coordHom x hx4').range := by
    rintro ⟨k, hk⟩
    have hk' : y = x ^ (Multiplicative.toAdd k).val := hk.symm
    apply hx1
    rw [← hxy, hk', commutatorElement_def]
    group
  have hsq : y ^ 2 = coordHom x hx4' (Multiplicative.ofAdd ((2 : ℕ) : ZMod (2 * 2))) := by
    rw [coordHom_apply, pow_two, hyy]
    have : (((2 : ℕ) : ZMod (2 * 2)).val) = 2 := by decide
    rw [this, pow_two]
  have hinvc : ∀ k : Multiplicative (ZMod (2 * 2)), y * coordHom x hx4' k * y⁻¹ =
      (coordHom x hx4' k)⁻¹ := fun k => hinv _
  exact ⟨CFSG.DisconnectedInvolutionGraph.Helpers.quaternionCoordinateEquiv 2 (coordHom x hx4') y
    hsq hinvc hinj hindex houtside⟩

end Q8

end CFSG.GH74.E2
