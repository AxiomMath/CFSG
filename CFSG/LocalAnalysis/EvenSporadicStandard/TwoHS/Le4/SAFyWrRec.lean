module

public import Mathlib.GroupTheory.RegularWreathProduct

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

@[expose] def eps : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem eps_ne_one : eps ≠ 1 := by decide

theorem eps_mul_eps : eps * eps = 1 := by decide

theorem eps_inv : eps⁻¹ = eps := by decide

theorem eq_one_or_eps (q : Multiplicative (ZMod 2)) : q = 1 ∨ q = eps := by
  revert q; decide

section Alg

variable {K : Type*} [Group K]

theorem wr_alg_A (x P Q R S : K) (hRQ : R * (x * Q * x⁻¹) = (x * Q * x⁻¹) * R) :
    P * R * (x * (Q * S) * x⁻¹) = P * (x * Q * x⁻¹) * (R * (x * S * x⁻¹)) := by
  calc P * R * (x * (Q * S) * x⁻¹) = P * (R * (x * Q * x⁻¹)) * (x * S * x⁻¹) := by group
    _ = P * ((x * Q * x⁻¹) * R) * (x * S * x⁻¹) := by rw [hRQ]
    _ = P * (x * Q * x⁻¹) * (R * (x * S * x⁻¹)) := by group

theorem wr_alg_B (x P Q R S : K) (hRQ : R * (x * Q * x⁻¹) = (x * Q * x⁻¹) * R) :
    P * R * (x * (Q * S) * x⁻¹) * x = P * (x * Q * x⁻¹) * (R * (x * S * x⁻¹) * x) := by
  calc P * R * (x * (Q * S) * x⁻¹) * x = P * (R * (x * Q * x⁻¹)) * (x * S * x⁻¹) * x := by group
    _ = P * ((x * Q * x⁻¹) * R) * (x * S * x⁻¹) * x := by rw [hRQ]
    _ = P * (x * Q * x⁻¹) * (R * (x * S * x⁻¹) * x) := by group

theorem wr_alg_C (x P Q R S : K) (hx : x * x = 1)
    (hSQ : S * (x * Q * x⁻¹) = (x * Q * x⁻¹) * S) (hSR : S * (x * R * x⁻¹) = (x * R * x⁻¹) * S) :
    P * S * (x * (Q * R) * x⁻¹) * x = P * (x * Q * x⁻¹) * x * (R * (x * S * x⁻¹)) := by
  have hxσ : x * (x * S * x⁻¹) = S * x := by
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    calc x * (x * S * x⁻¹) = (x * x) * S * x⁻¹ := by group
      _ = S * x := by rw [hx, one_mul, hxinv]
  have hS : S * ((x * Q * x⁻¹) * (x * R * x⁻¹)) = ((x * Q * x⁻¹) * (x * R * x⁻¹)) * S := by
    rw [← mul_assoc, hSQ, mul_assoc, hSR, ← mul_assoc]
  calc P * S * (x * (Q * R) * x⁻¹) * x
      = P * (S * ((x * Q * x⁻¹) * (x * R * x⁻¹))) * x := by group
    _ = P * (((x * Q * x⁻¹) * (x * R * x⁻¹)) * S) * x := by rw [hS]
    _ = P * (x * Q * x⁻¹) * (x * R * x⁻¹) * (S * x) := by group
    _ = P * (x * Q * x⁻¹) * (x * R * x⁻¹) * (x * (x * S * x⁻¹)) := by rw [hxσ]
    _ = P * (x * Q * x⁻¹) * x * (R * (x * S * x⁻¹)) := by group

theorem wr_alg_D (x P Q R S : K) (hx : x * x = 1)
    (hSQ : S * (x * Q * x⁻¹) = (x * Q * x⁻¹) * S) (hSR : S * (x * R * x⁻¹) = (x * R * x⁻¹) * S) :
    P * S * (x * (Q * R) * x⁻¹) = P * (x * Q * x⁻¹) * x * (R * (x * S * x⁻¹) * x) := by
  have hxσ : x * (x * S * x⁻¹) = S * x := by
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    calc x * (x * S * x⁻¹) = (x * x) * S * x⁻¹ := by group
      _ = S * x := by rw [hx, one_mul, hxinv]
  have hS : S * ((x * Q * x⁻¹) * (x * R * x⁻¹)) = ((x * Q * x⁻¹) * (x * R * x⁻¹)) * S := by
    rw [← mul_assoc, hSQ, mul_assoc, hSR, ← mul_assoc]
  calc P * S * (x * (Q * R) * x⁻¹)
      = P * (S * ((x * Q * x⁻¹) * (x * R * x⁻¹))) := by group
    _ = P * (((x * Q * x⁻¹) * (x * R * x⁻¹)) * S) := by rw [hS]
    _ = P * (x * Q * x⁻¹) * (x * R * x⁻¹) * (S * (x * x)) := by rw [hx]; group
    _ = P * (x * Q * x⁻¹) * (x * R * x⁻¹) * ((S * x) * x) := by group
    _ = P * (x * Q * x⁻¹) * (x * R * x⁻¹) * ((x * (x * S * x⁻¹)) * x) := by rw [hxσ]
    _ = P * (x * Q * x⁻¹) * x * (R * (x * S * x⁻¹) * x) := by group

end Alg

variable {K : Type*} [Group K] {D : Type*} [Group D]

@[expose] def wrMap (ρ : D →* K) (x : K)
    (w : RegularWreathProduct D (Multiplicative (ZMod 2))) : K :=
  ρ (w.left 1) * (x * ρ (w.left eps) * x⁻¹) * (if w.right = 1 then 1 else x)

theorem wrMap_mul (ρ : D →* K) (x : K) (hx : x * x = 1)
    (hc : ∀ a b : D, ρ a * (x * ρ b * x⁻¹) = (x * ρ b * x⁻¹) * ρ a)
    (u w : RegularWreathProduct D (Multiplicative (ZMod 2))) :
    wrMap ρ x (u * w) = wrMap ρ x u * wrMap ρ x w := by
  obtain ⟨f, p⟩ := u
  obtain ⟨g, q⟩ := w
  rcases eq_one_or_eps p with rfl | rfl <;> rcases eq_one_or_eps q with rfl | rfl
  · simp only [wrMap, RegularWreathProduct.mul_left, RegularWreathProduct.mul_right,
      Pi.mul_apply, mul_one, map_mul, inv_one, one_mul]
    simp
    exact wr_alg_A x _ _ _ _ (hc (g 1) (f eps))
  · simp only [wrMap, RegularWreathProduct.mul_left, RegularWreathProduct.mul_right,
      Pi.mul_apply, map_mul, inv_one, one_mul]
    simp [eps_ne_one]
    exact wr_alg_B x _ _ _ _ (hc (g 1) (f eps))
  · simp only [wrMap, RegularWreathProduct.mul_left, RegularWreathProduct.mul_right,
      Pi.mul_apply, mul_one, map_mul, eps_inv, eps_mul_eps]
    simp [eps_ne_one]
    exact wr_alg_C x _ _ _ _ hx (hc (g eps) (f eps)) (hc (g eps) (g 1))
  · simp only [wrMap, RegularWreathProduct.mul_left, RegularWreathProduct.mul_right,
      Pi.mul_apply, mul_one, map_mul, eps_inv, eps_mul_eps]
    simp [eps_ne_one]
    exact wr_alg_D x _ _ _ _ hx (hc (g eps) (f eps)) (hc (g eps) (g 1))

@[expose] def wrHom (ρ : D →* K) (x : K) (hx : x * x = 1)
    (hc : ∀ a b : D, ρ a * (x * ρ b * x⁻¹) = (x * ρ b * x⁻¹) * ρ a) :
    RegularWreathProduct D (Multiplicative (ZMod 2)) →* K where
  toFun := wrMap ρ x
  map_one' := by simp [wrMap]
  map_mul' := wrMap_mul ρ x hx hc

theorem wrMap_mk (ρ : D →* K) (x : K) (d₁ d₂ : D) (q : Multiplicative (ZMod 2)) :
    wrMap ρ x ⟨fun r => if r = 1 then d₁ else d₂, q⟩ =
      ρ d₁ * (x * ρ d₂ * x⁻¹) * (if q = 1 then 1 else x) := by
  simp [wrMap, eps_ne_one]

theorem wrHom_injective (ρ : D →* K) (x : K) (hx : x * x = 1)
    (hc : ∀ a b : D, ρ a * (x * ρ b * x⁻¹) = (x * ρ b * x⁻¹) * ρ a)
    (hρinj : Function.Injective ρ)
    (hinf : ∀ a b : D, ρ a = x * ρ b * x⁻¹ → ρ a = 1)
    (hxn : ∀ a b : D, x ≠ ρ a * (x * ρ b * x⁻¹)) :
    Function.Injective (wrHom ρ x hx hc) := by
  have hΦ : ∀ w, wrHom ρ x hx hc w = wrMap ρ x w := fun w => rfl
  rw [injective_iff_map_eq_one]
  intro w hw
  obtain ⟨f, p⟩ := w
  rw [hΦ] at hw
  rcases eq_one_or_eps p with rfl | rfl
  · simp only [wrMap, ↓reduceIte, mul_one] at hw
    have h1 : ρ (f 1) = (x * ρ (f eps) * x⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hw
    have h2 : ρ (f 1) = 1 := by
      refine hinf (f 1) (f eps)⁻¹ ?_
      rw [h1, map_inv]; group
    have h3 : x * ρ (f eps) * x⁻¹ = 1 := by
      rw [h2, one_mul] at hw; exact hw
    have h4 : ρ (f eps) = 1 := by
      have : ρ (f eps) = x⁻¹ * (x * ρ (f eps) * x⁻¹) * x := by group
      rw [this, h3]; group
    have hf1 : f 1 = 1 := hρinj (by rw [h2, map_one])
    have hfe : f eps = 1 := hρinj (by rw [h4, map_one])
    have hf : f = 1 := by
      funext q
      rcases eq_one_or_eps q with rfl | rfl
      · exact hf1
      · exact hfe
    rw [hf]; rfl
  · exfalso
    simp only [wrMap, eps_ne_one, ↓reduceIte] at hw
    have h2 : ρ (f 1) * (x * ρ (f eps) * x⁻¹) = x⁻¹ := eq_inv_of_mul_eq_one_left hw
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    apply hxn (f 1)⁻¹ (f eps)⁻¹
    rw [map_inv, map_inv]
    calc x = (x⁻¹)⁻¹ := (inv_inv x).symm
      _ = (ρ (f 1) * (x * ρ (f eps) * x⁻¹))⁻¹ := by rw [h2]
      _ = (x * ρ (f eps) * x⁻¹)⁻¹ * (ρ (f 1))⁻¹ := by rw [mul_inv_rev]
      _ = (ρ (f 1))⁻¹ * (x * ρ (f eps) * x⁻¹)⁻¹ :=
        (Commute.inv_inv (hc (f 1) (f eps))).eq.symm
      _ = (ρ (f 1))⁻¹ * (x * (ρ (f eps))⁻¹ * x⁻¹) := by group

end CFSG.EvenSporadicStandard.TwoHS
