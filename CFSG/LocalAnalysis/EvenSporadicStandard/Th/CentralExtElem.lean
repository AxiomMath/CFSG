module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSporadicStandard.ThStd

structure TwoStepData (E V : Type*) [Group E] [Group V] (θ : E →* V) (τ : E) : Prop where
  V_comm : ∀ u v : V, u * v = v * u
  V_sq : ∀ v : V, v * v = 1
  tau_ne : τ ≠ 1
  tau_central : ∀ e : E, τ * e = e * τ
  tau_ker : θ τ = 1
  ker : ∀ e : E, θ e = 1 → e = 1 ∨ e = τ

namespace TwoStepData

variable {E V : Type*} [Group E] [Group V] {θ : E →* V} {τ : E} (D : TwoStepData E V θ τ)

include D

theorem tau_mul_tau : τ * τ = 1 := by
  have h1 : θ (τ * τ) = 1 := by rw [map_mul, D.tau_ker, mul_one]
  rcases D.ker _ h1 with h | h
  · exact h
  · exfalso
    apply D.tau_ne
    have : τ * τ = τ * 1 := by rw [h, mul_one]
    exact mul_left_cancel this

theorem sq_cases (e : E) : e * e = 1 ∨ e * e = τ :=
  D.ker _ (by rw [map_mul]; exact D.V_sq _)

theorem comm_cases (a b : E) : a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = τ := by
  apply D.ker
  simp only [map_mul, map_inv]
  rw [D.V_comm (θ a) (θ b)]
  group

theorem comm_central (a b e : E) : (a * b * a⁻¹ * b⁻¹) * e = e * (a * b * a⁻¹ * b⁻¹) := by
  rcases D.comm_cases a b with h | h
  · rw [h]
    simp
  · rw [h]
    exact D.tau_central e

theorem commutator_eq_tau {a b : E} (ha : a * a = τ) (hb : b * b = τ)
    (hab : (a * b) * (a * b) = τ) : a * b * a⁻¹ * b⁻¹ = τ := by
  set c := a * b * a⁻¹ * b⁻¹ with hc
  have hcc : ∀ e : E, c * e = e * c := fun e => D.comm_central a b e
  have h1 : b * a = c⁻¹ * (a * b) := by
    rw [hc]
    group
  have h3 : c⁻¹ * a = a * c⁻¹ := ((show Commute c a from hcc a).inv_left).eq
  have h2 : (a * b) * (a * b) = c⁻¹ * (a * a) * (b * b) := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (c⁻¹ * (a * b)) * b := by rw [h1]
      _ = (a * c⁻¹) * (a * b) * b := by group
      _ = (c⁻¹ * a) * (a * b) * b := by rw [h3]
      _ = c⁻¹ * (a * a) * (b * b) := by group
  rw [h2, ha, hb, mul_assoc, D.tau_mul_tau, mul_one] at hab
  have : c = τ⁻¹ := by
    rw [← hab]
    simp
  rw [this]
  exact inv_eq_of_mul_eq_one_right D.tau_mul_tau

theorem theta_mul_ne_one {u v : E} (h : θ u ≠ θ v) : θ (u * v) ≠ 1 := by
  intro h1
  apply h
  rw [map_mul] at h1
  have : θ u = (θ v)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [this]
  exact inv_eq_of_mul_eq_one_right (D.V_sq _)

theorem sq_eq_one_of_transitive
    (hq : ∀ x y : E, θ x ≠ 1 → θ y ≠ 1 → (x * x = τ ↔ y * y = τ))
    {x y w : E} (hx : θ x ≠ 1) (hy : θ y ≠ 1) (hw : θ w ≠ 1)
    (hxy : θ x ≠ θ y) (hxw : θ x ≠ θ w) (hyw : θ y ≠ θ w) (hind : θ w ≠ θ x * θ y) :
    ∀ e : E, e * e = 1 := by
  have key : ∀ e : E, θ e ≠ 1 → e * e = 1 := by
    intro e he
    by_contra hne
    have hτe : e * e = τ := (D.sq_cases e).resolve_left hne
    have hall : ∀ u : E, θ u ≠ 1 → u * u = τ := fun u hu => (hq e u he hu).1 hτe
    have hcomm : ∀ u v : E, θ u ≠ 1 → θ v ≠ 1 → θ u ≠ θ v → u * v * u⁻¹ * v⁻¹ = τ :=
      fun u v hu hv huv =>
        D.commutator_eq_tau (hall u hu) (hall v hv) (hall (u * v) (D.theta_mul_ne_one huv))
    have h1 := hcomm x y hx hy hxy
    have h2 := hcomm x w hx hw hxw
    have hyw' : θ (y * w) ≠ 1 := D.theta_mul_ne_one hyw
    have hxyw : θ x ≠ θ (y * w) := by
      intro h
      apply hind
      rw [map_mul] at h
      calc θ w = (θ y * θ y) * θ w := by rw [D.V_sq, one_mul]
        _ = θ y * (θ y * θ w) := by rw [mul_assoc]
        _ = θ y * θ x := by rw [h]
        _ = θ x * θ y := D.V_comm _ _
    have h3 := hcomm x (y * w) hx hyw' hxyw
    have hbil : x * (y * w) * x⁻¹ * (y * w)⁻¹ =
        (x * y * x⁻¹ * y⁻¹) * (y * (x * w * x⁻¹ * w⁻¹) * y⁻¹) := by group
    rw [h3, h1, h2] at hbil
    have hconj : y * τ * y⁻¹ = τ := by
      rw [← D.tau_central y]
      group
    rw [hconj, D.tau_mul_tau] at hbil
    exact D.tau_ne hbil
  intro e
  by_cases he : θ e = 1
  · rcases D.ker e he with rfl | rfl
    · simp
    · exact D.tau_mul_tau
  · exact key e he

theorem mul_comm_of_transitive
    (hq : ∀ x y : E, θ x ≠ 1 → θ y ≠ 1 → (x * x = τ ↔ y * y = τ))
    {x y w : E} (hx : θ x ≠ 1) (hy : θ y ≠ 1) (hw : θ w ≠ 1)
    (hxy : θ x ≠ θ y) (hxw : θ x ≠ θ w) (hyw : θ y ≠ θ w) (hind : θ w ≠ θ x * θ y) (a b : E) :
    a * b = b * a := by
  have hsq := D.sq_eq_one_of_transitive hq hx hy hw hxy hxw hyw hind
  have h1 : (a * b) * (a * b) = 1 := hsq _
  have e1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a)
  have e2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b)
  have e3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
  have e4 : (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
  rw [e1, e2] at e4
  exact e3.symm.trans e4

end TwoStepData

end CFSG.EvenSporadicStandard.ThStd
