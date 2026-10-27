module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.SuzOuter

open Subgroup

variable {Q Q' : Type*} [Group Q] [Group Q']

structure OddCentralHom (φ : Q →* Q') : Prop where
  surjective : Function.Surjective φ
  central : ∀ k ∈ φ.ker, ∀ x : Q, k * x = x * k
  odd : Odd (Nat.card φ.ker)

namespace OddCentralHom

variable {φ : Q →* Q'} (h : OddCentralHom φ)

include h in
theorem eq_one_of_sq_eq_one {z : Q} (hz : z ∈ φ.ker) (hz2 : z * z = 1) : z = 1 := by
  have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
  have h2 : orderOf (⟨z, hz⟩ : φ.ker) ∣ Nat.card φ.ker := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h2
  have h3 : orderOf z = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h3 | h3
    · exact h3
    · rw [h3] at h2
      exact absurd (even_iff_two_dvd.2 h2) (Nat.not_even_iff_odd.2 h.odd)
  exact orderOf_eq_one_iff.1 h3

include h in
theorem eq_of_involutions {u u' : Q} (hu : u * u = 1) (hu' : u' * u' = 1) (he : φ u = φ u') :
    u = u' := by
  have hz : u⁻¹ * u' ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  have hc : (u⁻¹ * u') * u = u * (u⁻¹ * u') := h.central _ hz u
  have hsq : (u⁻¹ * u') * (u⁻¹ * u') = 1 := by
    have h1 : u' * u' = (u * u) * ((u⁻¹ * u') * (u⁻¹ * u')) := by
      calc u' * u' = (u * (u⁻¹ * u')) * (u * (u⁻¹ * u')) := by group
        _ = u * ((u⁻¹ * u') * u) * (u⁻¹ * u') := by group
        _ = u * (u * (u⁻¹ * u')) * (u⁻¹ * u') := by rw [hc]
        _ = (u * u) * ((u⁻¹ * u') * (u⁻¹ * u')) := by group
    rw [hu', hu, one_mul] at h1
    exact h1.symm
  exact inv_mul_eq_one.1 (h.eq_one_of_sq_eq_one hz hsq)

include h in
theorem exists_involution_lift [Finite Q] {v : Q'} (hv : v * v = 1) (hv1 : v ≠ 1) :
    ∃ u : Q, u * u = 1 ∧ u ≠ 1 ∧ φ u = v := by
  obtain ⟨u₀, rfl⟩ := h.surjective v
  have hsq : u₀ * u₀ ∈ φ.ker := by rw [MonoidHom.mem_ker, map_mul]; exact hv
  have hpow : (u₀ * u₀) ^ Nat.card φ.ker = 1 := by
    have := pow_card_eq_one' (G := φ.ker) (x := ⟨u₀ * u₀, hsq⟩)
    exact congrArg Subtype.val this
  obtain ⟨k, hk⟩ := h.odd
  have hφ : φ (u₀ ^ Nat.card φ.ker) = φ u₀ := by
    rw [map_pow, hk, pow_succ, pow_mul, pow_two, hv, one_pow, one_mul]
  refine ⟨u₀ ^ Nat.card φ.ker, ?_, fun h1 => hv1 ?_, hφ⟩
  · rw [← pow_add, ← two_mul, pow_mul, pow_two]
    exact hpow
  · rw [← hφ, h1, map_one]

include h in
theorem card_centralizer [Finite Q] {u : Q} (hu : u * u = 1) :
    Nat.card (centralizer ({u} : Set Q)) =
      Nat.card φ.ker * Nat.card (centralizer ({φ u} : Set Q')) := by
  set H : Subgroup Q := centralizer ({u} : Set Q) with hH
  let ψ : ↥H →* Q' := φ.comp H.subtype
  have hrange : ψ.range = centralizer ({φ u} : Set Q') := by
    ext v
    constructor
    · rintro ⟨y, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have hy := mem_centralizer_singleton_iff.1 y.2
      show φ y * φ u = φ u * φ y
      rw [← map_mul, ← map_mul, hy]
    · intro hv
      obtain ⟨y, rfl⟩ := h.surjective v
      have hvy : φ y * φ u = φ u * φ y := mem_centralizer_singleton_iff.1 hv
      have hu' : (y * u * y⁻¹) * (y * u * y⁻¹) = 1 := by
        calc (y * u * y⁻¹) * (y * u * y⁻¹) = y * (u * u) * y⁻¹ := by group
          _ = 1 := by rw [hu]; group
      have he : φ u = φ (y * u * y⁻¹) := by
        rw [map_mul, map_mul, map_inv, hvy, mul_inv_cancel_right]
      have h2 := h.eq_of_involutions hu hu' he
      refine ⟨⟨y, ?_⟩, rfl⟩
      rw [hH, mem_centralizer_singleton_iff]
      calc y * u = (y * u * y⁻¹) * y := by group
        _ = u * y := by rw [← h2]
  have hker : Nat.card ψ.ker = Nat.card φ.ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : Q), x.2⟩
        invFun := fun k => ⟨⟨(k : Q), ?_⟩, k.2⟩
        left_inv := fun x => rfl
        right_inv := fun k => rfl }
    rw [hH, mem_centralizer_singleton_iff]
    exact h.central _ k.2 u
  have hcard := Subgroup.card_ker_mul_card_range ψ
  rw [hker, hrange] at hcard
  exact hcard.symm

end OddCentralHom

end CFSG.EvenSporadicStandard.SuzOuter
