module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory.SteinbergBS

variable {X : Type*} [Group X]

section General

variable (t : MulAut X)

theorem inv_apply_mul_eq_iff (z w : X) :
    (t w)⁻¹ * w = (t z)⁻¹ * z ↔ t (w * z⁻¹) = w * z⁻¹ := by
  rw [map_mul, map_inv]
  constructor
  · intro h
    calc t w * (t z)⁻¹ = t w * ((t z)⁻¹ * z * z⁻¹) := by group
      _ = t w * ((t w)⁻¹ * w * z⁻¹) := by rw [h]
      _ = w * z⁻¹ := by group
  · intro h
    calc (t w)⁻¹ * w = (t w)⁻¹ * (w * z⁻¹) * z := by group
      _ = (t w)⁻¹ * (t w * (t z)⁻¹) * z := by rw [h]
      _ = (t z)⁻¹ * z := by group

variable {t}

theorem apply_apply_of_sq_eq_one (ht : t ^ 2 = 1) (x : X) : t (t x) = x := by
  rw [← MulAut.mul_apply, ← sq, ht, MulAut.one_apply]

theorem apply_inv_apply_mul (ht : t ^ 2 = 1) (z : X) :
    t ((t z)⁻¹ * z) = ((t z)⁻¹ * z)⁻¹ := by
  rw [map_mul, map_inv, apply_apply_of_sq_eq_one ht, mul_inv_rev, inv_inv]

end General

section Odd

variable (hX : Odd (Nat.card X))
include hX

theorem sq_pow_half_card (x : X) : (x ^ ((Nat.card X + 1) / 2)) ^ 2 = x := by
  obtain ⟨k, hk⟩ := hX
  rw [← pow_mul, hk, show (2 * k + 1 + 1) / 2 * 2 = 2 * k + 1 + 1 by omega, pow_succ, ← hk,
    pow_card_eq_one', one_mul]

theorem sq_pow_half_card' (x : X) : (x ^ 2) ^ ((Nat.card X + 1) / 2) = x := by
  rw [← pow_mul, mul_comm, pow_mul, sq_pow_half_card hX]

theorem eq_one_of_sq_eq_one {c : X} (hc : c ^ 2 = 1) : c = 1 := by
  rw [← sq_pow_half_card' hX c, hc, one_pow]

theorem exists_eq_inv_apply_mul {t : MulAut X} {x : X} (hx : t x = x⁻¹) :
    ∃ z : X, x = (t z)⁻¹ * z := by
  refine ⟨x ^ ((Nat.card X + 1) / 2), ?_⟩
  rw [map_pow, hx, inv_pow, inv_inv, ← sq, sq_pow_half_card hX]

theorem eq_one_of_apply_mul_eq_inv {t : MulAut X} {c x : X} (hc : t c = c) (hx : t x = x⁻¹)
    (hcx : t (c * x) = (c * x)⁻¹) : c = 1 := by
  rw [map_mul, hc, hx, mul_inv_rev] at hcx
  have h1 : x * c * x⁻¹ = c⁻¹ := by
    calc x * c * x⁻¹ = x * (c * x⁻¹) := by group
      _ = x * (x⁻¹ * c⁻¹) := by rw [hcx]
      _ = c⁻¹ := by group
  have h2 : Commute c (x * x) := by
    have h3 : x * x * c * (x * x)⁻¹ = c := by
      calc x * x * c * (x * x)⁻¹ = x * (x * c * x⁻¹) * x⁻¹ := by group
        _ = x * c⁻¹ * x⁻¹ := by rw [h1]
        _ = (x * c * x⁻¹)⁻¹ := by group
        _ = c := by rw [h1, inv_inv]
    calc c * (x * x) = x * x * c * (x * x)⁻¹ * (x * x) := by rw [h3]
      _ = x * x * c := by group
  have h4 : Commute c x := by
    have := h2.pow_right ((Nat.card X + 1) / 2)
    rwa [← sq, sq_pow_half_card' hX] at this
  have h5 : c = c⁻¹ := by rw [← h1, ← h4.eq, mul_inv_cancel_right]
  refine eq_one_of_sq_eq_one hX ?_
  calc c ^ 2 = c * c⁻¹ := by rw [sq, ← h5]
    _ = 1 := mul_inv_cancel c

theorem involutory_automorphism_inverted_count (t : MulAut X) (ht : t ^ 2 = 1) (Y : Subgroup X)
    (hY : ∀ y : X, y ∈ Y ↔ t y = y) :
    (∀ z w : X, w * z⁻¹ ∈ Y → (t w)⁻¹ * w = (t z)⁻¹ * z) ∧
    (∃ e : Quotient (QuotientGroup.rightRel Y) ≃ {x : X // t x = x⁻¹},
      ∀ z : X, (e (Quotient.mk _ z) : X) = (t z)⁻¹ * z) ∧
    Nat.card {x : X // t x = x⁻¹} = Y.index ∧
    (∀ x : X, t x = x⁻¹ → ∃ z : X, x = (t z)⁻¹ * z) ∧
    (∀ z : X, ∃! x : X, t x = x⁻¹ ∧ x * z⁻¹ ∈ Y) ∧
    (∀ z : X, ∃! x : X, t x = x⁻¹ ∧ z⁻¹ * x ∈ Y) := by
  have : Finite X := Nat.finite_of_card_ne_zero hX.pos.ne'
  have hconst : ∀ z w : X, w * z⁻¹ ∈ Y → (t w)⁻¹ * w = (t z)⁻¹ * z := fun z w h =>
    (inv_apply_mul_eq_iff t z w).2 ((hY _).1 h)
  let F : Quotient (QuotientGroup.rightRel Y) → {x : X // t x = x⁻¹} :=
    Quotient.lift (fun z => ⟨(t z)⁻¹ * z, apply_inv_apply_mul ht z⟩) fun a b hab =>
      Subtype.ext (hconst a b (QuotientGroup.rightRel_apply.1 hab)).symm
  have hFinj : Function.Injective F := by
    rintro ⟨a⟩ ⟨b⟩ h
    have h' : (t b)⁻¹ * b = (t a)⁻¹ * a := (congrArg Subtype.val h).symm
    exact Quotient.sound (QuotientGroup.rightRel_apply.2 ((hY _).2
      ((inv_apply_mul_eq_iff t a b).1 h')))
  have hFsurj : Function.Surjective F := by
    rintro ⟨x, hx⟩
    obtain ⟨z, hz⟩ := exists_eq_inv_apply_mul hX hx
    exact ⟨Quotient.mk _ z, Subtype.ext hz.symm⟩
  let e := Equiv.ofBijective F ⟨hFinj, hFsurj⟩
  have hcard : Nat.card {x : X // t x = x⁻¹} = Y.index := by
    rw [← Nat.card_congr e, Subgroup.index]
    exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Y)
  have hright : ∀ z : X, ∃! x : X, t x = x⁻¹ ∧ x * z⁻¹ ∈ Y := by
    have huniq : ∀ x₁ x₂ : X, t x₁ = x₁⁻¹ → t x₂ = x₂⁻¹ → x₂ * x₁⁻¹ ∈ Y → x₂ = x₁ := by
      intro x₁ x₂ h₁ h₂ h
      have hc := eq_one_of_apply_mul_eq_inv hX ((hY _).1 h) h₁ (by rwa [inv_mul_cancel_right])
      rwa [mul_inv_eq_one] at hc
    let g : {x : X // t x = x⁻¹} → Quotient (QuotientGroup.rightRel Y) :=
      fun x => Quotient.mk _ x.1
    have hginj : Function.Injective g := fun x₁ x₂ h =>
      Subtype.ext (huniq _ _ x₂.2 x₁.2 (QuotientGroup.rightRel_apply.1 (Quotient.exact h.symm)))
    have : Finite (Quotient (QuotientGroup.rightRel Y)) := Quotient.finite _
    have hgbij := hginj.bijective_of_nat_card_le (Nat.card_congr e).le
    intro z
    obtain ⟨⟨x, hx⟩, hxz⟩ := hgbij.2 (Quotient.mk _ z)
    have hzx : z * x⁻¹ ∈ Y := QuotientGroup.rightRel_apply.1 (Quotient.exact hxz)
    refine ⟨x, ⟨hx, by simpa only [mul_inv_rev, inv_inv] using Y.inv_mem hzx⟩, ?_⟩
    rintro x' ⟨hx', hx'z⟩
    refine huniq x x' hx hx' ?_
    have := Y.mul_mem hx'z hzx
    rwa [mul_assoc, inv_mul_cancel_left] at this
  refine ⟨hconst, ⟨e, fun z => rfl⟩, hcard, fun x hx => exists_eq_inv_apply_mul hX hx, hright,
    fun z => ?_⟩
  obtain ⟨x, ⟨hx, hxz⟩, hxu⟩ := hright z⁻¹
  refine ⟨x⁻¹, ⟨by rw [map_inv, hx], ?_⟩, ?_⟩
  · have := Y.inv_mem hxz
    rwa [inv_inv, mul_inv_rev] at this
  · rintro y ⟨hy, hyz⟩
    have h1 : t y⁻¹ = y⁻¹⁻¹ := by rw [map_inv, hy]
    have h2 : y⁻¹ * z⁻¹⁻¹ ∈ Y := by
      have := Y.inv_mem hyz
      rwa [mul_inv_rev] at this
    rw [← hxu y⁻¹ ⟨h1, h2⟩, inv_inv]

theorem card_inverted_mul_card_fixed {t : MulAut X} (ht : t ^ 2 = 1) :
    Nat.card {x : X // t x = x⁻¹} * Nat.card (t.toMonoidHom.eqLocus (MonoidHom.id X)) =
      Nat.card X := by
  rw [(involutory_automorphism_inverted_count hX t ht (t.toMonoidHom.eqLocus (MonoidHom.id X))
    fun _ => Iff.rfl).2.2.1, Subgroup.index_mul_card]

end Odd

end CFSG.GroupTheory.SteinbergBS
