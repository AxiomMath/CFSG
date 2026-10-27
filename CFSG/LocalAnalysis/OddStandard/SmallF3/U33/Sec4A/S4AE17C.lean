module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem e17_fpf_split {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) {ρ u : G}
    (hρX : ∀ x ∈ X, ρ * x * ρ⁻¹ ∈ X) (huX : ∀ x ∈ X, u * x * u⁻¹ ∈ X)
    (hρ3 : ρ ^ 3 = 1) (hu2 : u * u = 1) (huρ : u * ρ * u⁻¹ = ρ⁻¹)
    (hfix : ∀ x ∈ X, ρ * x = x * ρ → x = 1) :
    ∀ x ∈ X, ∃ c₁ ∈ X, ∃ c₂ ∈ X, u * c₁ = c₁ * u ∧ u * c₂ = c₂ * u ∧
      x = c₁ * (ρ * c₂ * ρ⁻¹) := by
  intro x hx
  haveI : IsMulCommutative X :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (hXc a a.2 b b.2))
  have hρ3' : ρ * ρ * ρ = 1 := by rw [← pow_three']; exact hρ3
  have hρinv : ρ⁻¹ = ρ * ρ := inv_eq_of_mul_eq_one_left hρ3'
  have hρinv2 : ρ⁻¹ * ρ⁻¹ = ρ := by
    calc ρ⁻¹ * ρ⁻¹ = (ρ * ρ) * (ρ * ρ) := by rw [hρinv]
      _ = (ρ * ρ * ρ) * ρ := by group
      _ = 1 * ρ := by rw [hρ3']
      _ = ρ := by group
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2
  let R : X →* X :=
    { toFun := fun a => ⟨ρ * (a : G) * ρ⁻¹, hρX a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show ρ * ((a : G) * (b : G)) * ρ⁻¹ =
          (ρ * (a : G) * ρ⁻¹) * (ρ * (b : G) * ρ⁻¹)
        group) }
  let S : X →* X :=
    { toFun := fun a => ⟨u * (a : G) * u⁻¹, huX a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show u * ((a : G) * (b : G)) * u⁻¹ =
          (u * (a : G) * u⁻¹) * (u * (b : G) * u⁻¹)
        group) }
  let N : X → X := fun a => R (R a) * (R a)⁻¹
  have hR3 : ∀ a : X, R (R (R a)) = a := fun a => Subtype.ext (by
    show ρ * (ρ * (ρ * (a : G) * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ = (a : G)
    calc ρ * (ρ * (ρ * (a : G) * ρ⁻¹) * ρ⁻¹) * ρ⁻¹
        = (ρ * ρ * ρ) * (a : G) * (ρ⁻¹ * ρ⁻¹ * ρ⁻¹) := by group
      _ = 1 * (a : G) * 1 := by
            rw [hρ3', show ρ⁻¹ * ρ⁻¹ * ρ⁻¹ = 1 by
              rw [show ρ⁻¹ * ρ⁻¹ * ρ⁻¹ = ρ⁻¹ * (ρ⁻¹ * ρ⁻¹) by group]
              rw [hρinv2, hρinv, hρ3']]
      _ = (a : G) := by group)
  have hS2 : ∀ a : X, S (S a) = a := fun a => Subtype.ext (by
    show u * (u * (a : G) * u⁻¹) * u⁻¹ = (a : G)
    calc u * (u * (a : G) * u⁻¹) * u⁻¹
        = (u * u) * (a : G) * (u⁻¹ * u⁻¹) := by group
      _ = 1 * (a : G) * 1 := by
            rw [hu2, show u⁻¹ * u⁻¹ = 1 by rw [huinv, hu2]]
      _ = (a : G) := by group)
  have hF2 : ∀ a : X, a * R a * R (R a) = 1 := fun a => by
    have hmem : ((a : G) * (R a : G) * (R (R a) : G)) ∈ X :=
      X.mul_mem (X.mul_mem a.2 (R a).2) (R (R a)).2
    have hry : ρ * ((a : G) * (R a : G) * (R (R a) : G)) * ρ⁻¹ =
        (a : G) * (R a : G) * (R (R a) : G) := by
      rw [show ∀ p q s : G, ρ * (p * q * s) * ρ⁻¹ =
          (ρ * p * ρ⁻¹) * (ρ * q * ρ⁻¹) * (ρ * s * ρ⁻¹) from
        fun p q s => by group]
      change (R a : G) * (R (R a) : G) * (R (R (R a)) : G) =
        (a : G) * (R a : G) * (R (R a) : G)
      rw [hR3 a]
      exact congrArg Subtype.val
        (by ac_rfl : R a * R (R a) * a = a * R a * R (R a))
    have hcomm : ρ * ((a : G) * (R a : G) * (R (R a) : G)) =
        ((a : G) * (R a : G) * (R (R a) : G)) * ρ :=
      (mul_inv_eq_iff_eq_mul).mp hry
    exact Subtype.ext (hfix _ hmem hcomm)
  have hconjρ : ∀ z : G, ρ⁻¹ * z * ρ = ρ * (ρ * z * ρ⁻¹) * ρ⁻¹ := by
    intro z
    calc ρ⁻¹ * z * ρ = (ρ * ρ) * z * (ρ⁻¹ * ρ⁻¹) := by rw [← hρinv, hρinv2]
      _ = ρ * (ρ * z * ρ⁻¹) * ρ⁻¹ := by group
  have hF3a : ∀ a : X, S (R a) = R (R (S a)) := fun a => Subtype.ext (by
    show u * (ρ * (a : G) * ρ⁻¹) * u⁻¹ =
      ρ * (ρ * (u * (a : G) * u⁻¹) * ρ⁻¹) * ρ⁻¹
    calc u * (ρ * (a : G) * ρ⁻¹) * u⁻¹
        = (u * ρ * u⁻¹) * (u * (a : G) * u⁻¹) * (u * ρ * u⁻¹)⁻¹ := by group
      _ = ρ⁻¹ * (u * (a : G) * u⁻¹) * ρ := by rw [huρ]; group
      _ = ρ * (ρ * (u * (a : G) * u⁻¹) * ρ⁻¹) * ρ⁻¹ := hconjρ _)
  have hF3b : ∀ a : X, S (R (R a)) = R (S a) := fun a => by
    calc S (R (R a)) = R (R (S (R a))) := hF3a (R a)
      _ = R (R (R (R (S a)))) := by rw [hF3a a]
      _ = R (S a) := by rw [hR3 (R (S a))]
  have hF4 : ∀ a : X, N (S a) = (S (N a))⁻¹ := fun a => by
    show R (R (S a)) * (R (S a))⁻¹ = (S (R (R a) * (R a)⁻¹))⁻¹
    rw [map_mul, map_inv, mul_inv_rev, inv_inv, hF3a a, hF3b a]
  have hRN : ∀ a : X, R (N a) = a * (R (R a))⁻¹ := fun a => by
    show R (R (R a) * (R a)⁻¹) = a * (R (R a))⁻¹
    rw [map_mul, map_inv, hR3 a]
  have hRRN : ∀ a : X, R (R (N a)) = R a * a⁻¹ := fun a => by
    rw [hRN a, map_mul, map_inv, hR3 a]
  have hF5 : ∀ a : X, N (N a) = (a * a * a)⁻¹ := fun a => by
    show R (R (N a)) * (R (N a))⁻¹ = (a * a * a)⁻¹
    rw [hRRN a, hRN a, mul_inv_rev, inv_inv]
    have hswap : R a * R (R a) = a⁻¹ := by
      calc R a * R (R a) = a⁻¹ * (a * R a * R (R a)) := by group
        _ = a⁻¹ * 1 := by rw [hF2 a]
        _ = a⁻¹ := by group
    calc (R a * a⁻¹) * (R (R a) * a⁻¹)
        = (R a * R (R a)) * (a⁻¹ * a⁻¹) := by ac_rfl
      _ = a⁻¹ * (a⁻¹ * a⁻¹) := by rw [hswap]
      _ = (a * a * a)⁻¹ := by rw [mul_inv_rev, mul_inv_rev]
  have hcube : ∀ a : X, a * a * a = 1 → a = 1 := fun a ha => by
    have ha3 : a ^ 3 = 1 := by rw [pow_three']; exact ha
    have h3 : orderOf a ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr ha3
    obtain ⟨k, hk⟩ := hX.exists_pow_pow_eq_one a
    have h2 : orderOf a ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
    have hcop : Nat.Coprime 3 (2 ^ k) :=
      Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two (by decide : ¬ 2 ∣ 3)
    have h1 : orderOf a ∣ 1 := by
      rw [← Nat.coprime_iff_gcd_eq_one.mp hcop]
      exact Nat.dvd_gcd h3 h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hinj : Function.Injective N := fun a b hab => by
    have h3 : a * a * a = b * b * b := by
      have h := congrArg N hab
      rw [hF5 a, hF5 b] at h
      exact inv_inj.mp h
    have hz : (a * b⁻¹) * (a * b⁻¹) * (a * b⁻¹) = 1 := by
      have hp : (a * b⁻¹) * (a * b⁻¹) * (a * b⁻¹) =
          (a * a * a) * (b * b * b)⁻¹ := by
        calc (a * b⁻¹) * (a * b⁻¹) * (a * b⁻¹)
            = (a * a * a) * (b⁻¹ * b⁻¹ * b⁻¹) := by ac_rfl
          _ = (a * a * a) * (b * b * b)⁻¹ := by
                rw [show b⁻¹ * b⁻¹ * b⁻¹ = (b * b * b)⁻¹ by
                  rw [mul_inv_rev, mul_inv_rev, mul_assoc]]
      rw [hp, h3, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hcube (a * b⁻¹) hz)
  let x' : X := ⟨x, hx⟩
  have hsurj : Function.Surjective N := (Finite.injective_iff_surjective (f := N)).mp hinj
  obtain ⟨c₂, hc₂⟩ := hsurj (S x' * x'⁻¹)
  have hSc₂ : S c₂ = c₂ := by
    apply hinj
    rw [hF4 c₂, hc₂, map_mul, map_inv, hS2 x', mul_inv_rev, inv_inv]
  let c₁ : X := x' * (R c₂)⁻¹
  have hSc₁ : S c₁ = c₁ := by
    show S (x' * (R c₂)⁻¹) = x' * (R c₂)⁻¹
    rw [map_mul, map_inv, hF3a c₂, hSc₂]
    have hEq : S x' * x'⁻¹ = R (R c₂) * (R c₂)⁻¹ := by rw [← hc₂]
    calc S x' * (R (R c₂))⁻¹
        = (S x' * x'⁻¹) * (x' * (R (R c₂))⁻¹) := by group
      _ = (R (R c₂) * (R c₂)⁻¹) * (x' * (R (R c₂))⁻¹) := by rw [hEq]
      _ = x' * (R (R c₂) * (R (R c₂))⁻¹) * (R c₂)⁻¹ := by ac_rfl
      _ = x' * (R c₂)⁻¹ := by group
  refine ⟨c₁, c₁.2, c₂, c₂.2, ?_, ?_, ?_⟩
  · exact (mul_inv_eq_iff_eq_mul).mp (congrArg Subtype.val hSc₁)
  · exact (mul_inv_eq_iff_eq_mul).mp (congrArg Subtype.val hSc₂)
  · have hc₁val : (c₁ : G) = x * (ρ * (c₂ : G) * ρ⁻¹)⁻¹ := by
      change (x' : G) * ((R c₂ : X) : G)⁻¹ = x * (ρ * (c₂ : G) * ρ⁻¹)⁻¹
      rw [show ((R c₂ : X) : G) = ρ * (c₂ : G) * ρ⁻¹ from rfl]
    rw [hc₁val]; group

theorem e17_card_le_sq {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) {ρ u : G}
    (hρX : ∀ x ∈ X, ρ * x * ρ⁻¹ ∈ X) (huX : ∀ x ∈ X, u * x * u⁻¹ ∈ X)
    (hρ3 : ρ ^ 3 = 1) (hu2 : u * u = 1) (huρ : u * ρ * u⁻¹ = ρ⁻¹)
    (hfix : ∀ x ∈ X, ρ * x = x * ρ → x = 1) :
    Nat.card X ≤ Nat.card ↥(X ⊓ centralizer ({u} : Set G)) *
      Nat.card ↥(X ⊓ centralizer ({u} : Set G)) := by
  let C : Subgroup G := X ⊓ centralizer ({u} : Set G)
  let Φ : ↥C × ↥C → ↥X := fun p =>
    ⟨(p.1 : G) * (ρ * (p.2 : G) * ρ⁻¹),
      X.mul_mem (Subgroup.mem_inf.mp p.1.2).1
        (hρX _ (Subgroup.mem_inf.mp p.2.2).1)⟩
  have hsurj : Function.Surjective Φ := by
    rintro ⟨y, hy⟩
    obtain ⟨c₁, hc₁X, c₂, hc₂X, hc₁u, hc₂u, hsplit⟩ :=
      e17_fpf_split hX hXc hρX huX hρ3 hu2 huρ hfix y hy
    exact ⟨(⟨c₁, Subgroup.mem_inf.mpr ⟨hc₁X,
        Subgroup.mem_centralizer_singleton_iff.mpr hc₁u.symm⟩⟩,
      ⟨c₂, Subgroup.mem_inf.mpr ⟨hc₂X,
        Subgroup.mem_centralizer_singleton_iff.mpr hc₂u.symm⟩⟩),
      Subtype.ext hsplit.symm⟩
  have h := Nat.card_le_card_of_surjective Φ hsurj
  rw [Nat.card_prod] at h
  simpa [C] using h

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
