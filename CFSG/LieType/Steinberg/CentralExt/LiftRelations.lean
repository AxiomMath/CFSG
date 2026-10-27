module

public import CFSG.LieType.Steinberg.CentralExt.WeylLift

public section

open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.LiftRel

attribute [local instance] TorusLift.centerCommGroup

theorem commutatorElement_commutatorElement_eq {E : Type*} [Group E] {k : Type*} [Neg k]
    {A B D : E} {W : k → E} {c : k} (hAD : A * D = D * A) (hBW : ∀ w, B * W w = W w * B)
    (hBD : ⁅B, D⁆ = W c) (hBD' : ⁅B⁻¹, D⁆ = W (-c)) (hW : W (-c) * W c = 1)
    (hAz : A * ⁅A⁻¹, W (-c)⁆ = ⁅A⁻¹, W (-c)⁆ * A)
    (hBz : B * ⁅A⁻¹, W (-c)⁆ = ⁅A⁻¹, W (-c)⁆ * B) :
    ⁅⁅A, B⁆, D⁆ = ⁅A⁻¹, W (-c)⁆ := by
  set z := ⁅A⁻¹, W (-c)⁆ with hz
  have s1 : B⁻¹ * D * B = W (-c) * D := by
    have h := hBD'
    rw [commutatorElement_def, inv_inv] at h
    calc B⁻¹ * D * B = B⁻¹ * D * B * D⁻¹ * D := by group
      _ = W (-c) * D := by rw [h]
  have s1' : B * D * B⁻¹ = W c * D := by
    have h := hBD
    rw [commutatorElement_def] at h
    calc B * D * B⁻¹ = B * D * B⁻¹ * D⁻¹ * D := by group
      _ = W c * D := by rw [h]
  have hAD' : A⁻¹ * D * A = D := by rw [mul_assoc, ← hAD, inv_mul_cancel_left]
  have s2 : A⁻¹ * W (-c) * A = z * W (-c) := by
    rw [hz, commutatorElement_def, inv_inv]
    group
  have hBz' : B * z * B⁻¹ = z := by rw [hBz, mul_inv_cancel_right]
  have hBW' : B * W (-c) * B⁻¹ = W (-c) := by rw [hBW, mul_inv_cancel_right]
  have hAz' : A * z * A⁻¹ = z := by rw [hAz, mul_inv_cancel_right]
  have hAD'' : A * D * A⁻¹ = D := by rw [hAD, mul_inv_cancel_right]
  calc ⁅⁅A, B⁆, D⁆ = A * (B * (A⁻¹ * (B⁻¹ * D * B) * A) * B⁻¹) * A⁻¹ * D⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = A * (B * ((A⁻¹ * W (-c) * A) * (A⁻¹ * D * A)) * B⁻¹) * A⁻¹ * D⁻¹ := by
        rw [s1]
        group
    _ = A * ((B * z * B⁻¹) * (B * W (-c) * B⁻¹) * (B * D * B⁻¹)) * A⁻¹ * D⁻¹ := by
        rw [s2, hAD']
        group
    _ = (A * z * A⁻¹) * (A * D * A⁻¹) * D⁻¹ := by
        have e : z * W (-c) * (W c * D) = z * D := by
          rw [mul_assoc z, ← mul_assoc (W (-c)), hW, one_mul]
        rw [hBz', hBW', s1', e]
        group
    _ = z := by rw [hAz', hAD'', mul_inv_cancel_right]

variable {E G : Type*} [Group E] [Group G] {π : E →* G} (hcen : π.ker ≤ Subgroup.center E)
include hcen

theorem commute_of_rev_sep_elem {k : Type*} [Field k] {x : k → G} {X : k → E}
    (hX : ∀ s t, X (s + t) = X s * X t) (hπX : ∀ s, π (X s) = x s) {z : E}
    (hxz : ∀ s, x s * π z = π z * x s) {e : E} {a : k} (ha : a ≠ 1)
    (h1 : ∀ s, e * X s * e⁻¹ = X (a * s)) (h2 : π (e * z * e⁻¹) = π z) (s : k) :
    X s * z = z * X s := by
  have hc : ∀ s, ⁅X s, z⁆ ∈ Subgroup.center E := fun s => hcen (by
    rw [MonoidHom.mem_ker, map_commutatorElement, hπX, commutatorElement_eq_one_iff_mul_comm]
    exact hxz s)
  have hadd : ∀ s s', ⁅X (s + s'), z⁆ = ⁅X s, z⁆ * ⁅X s', z⁆ := fun s s' => by
    rw [hX]
    exact TorusLift.commutatorElement_mul_left_of_central (hc s')
  have hinv : ∀ s, ⁅X (a * s), z⁆ = ⁅X s, z⁆ := fun s => by
    have e1 : e * ⁅X s, z⁆ * e⁻¹ = ⁅X (a * s), z⁆ := by
      rw [conjugate_commutatorElement, h1]
      exact TorusLift.commutatorElement_eq_of_map_eq hcen rfl h2
    rw [← e1, Subgroup.mem_center_iff.1 (hc s) e, mul_inv_cancel_right]
  have h0 : ∀ s, ⁅X ((a - 1) * s), z⁆ = 1 := fun s => by
    have h := hadd ((a - 1) * s) s
    rw [show (a - 1) * s + s = a * s by ring, hinv] at h
    exact right_eq_mul.1 h
  have h0s := h0 ((a - 1)⁻¹ * s)
  rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.2 ha), one_mul] at h0s
  exact commutatorElement_eq_one_iff_mul_comm.1 h0s

theorem commutatorElement_eq_of_sep {k : Type*} [Field k] {X Y Z : k → E} {C : k}
    (hY : ∀ s t, Y (s + t) = Y s * Y t) (hZ : ∀ s t, Z (s + t) = Z s * Z t)
    (hπ : ∀ u v, π ⁅X u, Y v⁆ = π (Z (C * u * v)))
    (hYZ : ∀ v w, Y v * Z w = Z w * Y v) {e : E} {b : k} (hb : b ≠ 1)
    (h1 : ∀ u, e * X u * e⁻¹ = X u) (h2 : ∀ v, e * Y v * e⁻¹ = Y (b * v))
    (h3 : ∀ w, e * Z w * e⁻¹ = Z (b * w)) (u v : k) :
    ⁅X u, Y v⁆ = Z (C * u * v) := by
  set d : k → E := fun v => ⁅X u, Y v⁆ * (Z (C * u * v))⁻¹ with hd
  have hc : ∀ v, d v ∈ Subgroup.center E := fun v => hcen (by
    rw [MonoidHom.mem_ker, hd, map_mul, map_inv, hπ, mul_inv_cancel])
  have hdz : ∀ v g, g * d v = d v * g := fun v g => Subgroup.mem_center_iff.1 (hc v) g
  have hcomm : ∀ v, ⁅X u, Y v⁆ = d v * Z (C * u * v) := fun v => by
    simp only [hd, inv_mul_cancel_right]
  have hadd : ∀ v v', d (v + v') = d v * d v' := fun v v' => by
    have e1 : ⁅X u, Y (v + v')⁆ = ⁅X u, Y v⁆ * (Y v * ⁅X u, Y v'⁆ * (Y v)⁻¹) := by
      rw [hY]
      simp only [commutatorElement_def]
      group
    have e2 : Y v * ⁅X u, Y v'⁆ * (Y v)⁻¹ = d v' * Z (C * u * v') := by
      rw [hcomm v', ← mul_assoc, hdz v' (Y v), mul_assoc (d v'), mul_assoc (d v'), hYZ,
        mul_inv_cancel_right]
    rw [hcomm (v + v'), hcomm v, e2, mul_add, hZ] at e1
    have e3 : d (v + v') * (Z (C * u * v) * Z (C * u * v')) =
        d v * d v' * (Z (C * u * v) * Z (C * u * v')) := by
      rw [e1, mul_assoc (d v), ← mul_assoc (Z (C * u * v)), hdz v' (Z (C * u * v))]
      group
    exact mul_right_cancel e3
  have htor : ∀ v, d (b * v) = d v := fun v => by
    have e3 : e * d v * e⁻¹ = d (b * v) := by
      have : e * d v * e⁻¹ = (e * ⁅X u, Y v⁆ * e⁻¹) * (e * Z (C * u * v) * e⁻¹)⁻¹ := by
        simp only [hd]
        group
      rw [this, conjugate_commutatorElement, h1, h2, h3, show b * (C * u * v) = C * u * (b * v) by
        ring]
    rw [← e3, hdz v e, mul_inv_cancel_right]
  have h0 : ∀ v, d ((b - 1) * v) = 1 := fun v => by
    have h := hadd ((b - 1) * v) v
    rw [show (b - 1) * v + v = b * v by ring, htor] at h
    exact right_eq_mul.1 h
  have hv := h0 ((b - 1)⁻¹ * v)
  rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.2 hb), one_mul] at hv
  rw [hcomm v, hv, one_mul]

theorem commPairing_eq_zero_of_card_three {k : Type} [Field k] [Finite k] (hk : Nat.card k = 3)
    (hπ : Function.Surjective π) {x : k → G} (hx : ∀ s t, x (s + t) = x s * x t) :
    TorusLift.commPairing hcen hπ hx = 0 := by
  refine AddMonoidHom.ext fun s => AddMonoidHom.ext fun t => ?_
  have h11 := TorusLift.commPairing_self hcen hπ hx 1
  rcases WeylLift.eq_zero_or_one_or_neg_one hk s with rfl | rfl | rfl <;>
    rcases WeylLift.eq_zero_or_one_or_neg_one hk t with rfl | rfl | rfl <;>
    simp [h11]

end CFSG.LieType.Steinberg.CentralExt.LiftRel
