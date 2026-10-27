module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup
open scoped Pointwise

section Cohom

variable {G : Type*} [Group G]

@[expose] def HOneTrivial (u : G) (Q : Subgroup G) : Prop :=
  ∀ q ∈ Q, q * (u * q * u⁻¹) = 1 → ∃ p ∈ Q, q = p⁻¹ * (u * p * u⁻¹)

theorem mul_comm_of_mul_self_eq_one {Z : Subgroup G} (hZ2 : ∀ z ∈ Z, z * z = 1) {a b : G}
    (ha : a ∈ Z) (hb : b ∈ Z) : a * b = b * a := by
  have h1 := hZ2 (a * b) (mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hZ2 a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hZ2 b hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = b * a := by rw [mul_inv_rev, ha', hb']

theorem hOneTrivial_of_card_sq_le {Z : Subgroup G} [Finite Z] {u : G} (hu2 : u * u = 1)
    (hZ2 : ∀ z ∈ Z, z * z = 1) (huZ : ∀ z ∈ Z, u * z * u⁻¹ ∈ Z)
    (hcard : Nat.card (Z ⊓ centralizer ({u} : Set G) : Subgroup G) ^ 2 ≤ Nat.card Z) :
    HOneTrivial u Z := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  let f : Z →* Z :=
    { toFun := fun r => ⟨r * (u * r * u⁻¹), mul_mem r.2 (huZ r r.2)⟩
      map_one' := by ext; simp
      map_mul' := fun r s => by
        ext
        simp only [Subgroup.coe_mul]
        have h1 := mul_comm_of_mul_self_eq_one hZ2 s.2 (huZ r r.2)
        calc (r : G) * s * (u * (r * s) * u⁻¹) =
              r * (s * (u * r * u⁻¹)) * (u * s * u⁻¹) := by group
          _ = r * ((u * r * u⁻¹) * s) * (u * s * u⁻¹) := by rw [h1]
          _ = r * (u * r * u⁻¹) * (s * (u * s * u⁻¹)) := by group }
  have hf : ∀ r : Z, ((f r : Z) : G) = r * (u * r * u⁻¹) := fun r => rfl
  have hker : ∀ r : Z, f r = 1 ↔ (r : G) ∈ centralizer ({u} : Set G) := by
    intro r
    rw [mem_centralizer_singleton_iff, ← Subtype.coe_inj, hf, OneMemClass.coe_one]
    have hr : (r : G)⁻¹ = r := inv_eq_of_mul_eq_one_right (hZ2 r r.2)
    constructor
    · intro h
      have h2 : u * r * u⁻¹ = r := (eq_inv_of_mul_eq_one_right h).trans hr
      calc (r : G) * u = u * r * u⁻¹ * u := by rw [h2]
        _ = u * r := by group
    · intro h
      calc (r : G) * (u * r * u⁻¹) = r * (r * u * u⁻¹) := by rw [h]
        _ = r * r := by group
        _ = 1 := hZ2 r r.2
  have hle : f.range ≤ f.ker := by
    rintro _ ⟨r, rfl⟩
    rw [MonoidHom.mem_ker, ← Subtype.coe_inj, hf, hf, OneMemClass.coe_one]
    have hr : u * (u * r * u⁻¹) * u⁻¹ = r := by
      rw [hu']
      calc u * (u * r * u) * u = (u * u) * r * (u * u) := by group
        _ = r := by rw [hu2]; group
    have h3 := mul_comm_of_mul_self_eq_one hZ2 (huZ r r.2) r.2
    calc (r : G) * (u * r * u⁻¹) * (u * (r * (u * r * u⁻¹)) * u⁻¹) =
        r * (u * r * u⁻¹) * ((u * r * u⁻¹) * (u * (u * r * u⁻¹) * u⁻¹)) := by group
      _ = r * (u * r * u⁻¹) * ((u * r * u⁻¹) * r) := by rw [hr]
      _ = r * ((u * r * u⁻¹) * (u * r * u⁻¹)) * r := by group
      _ = 1 := by rw [hZ2 _ (huZ r r.2), mul_one, hZ2 r r.2]
  have hkc : Nat.card f.ker = Nat.card (Z ⊓ centralizer ({u} : Set G) : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, mem_inf.2 ⟨x.1.2, (hker x.1).1 x.2⟩⟩
        invFun := fun y => ⟨⟨y.1, (mem_inf.1 y.2).1⟩, (hker _).2 (mem_inf.1 y.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hmul := Subgroup.card_ker_mul_card_range f
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have hge : Nat.card f.ker ≤ Nat.card f.range := by
    rw [← hkc, ← hmul, sq] at hcard
    exact Nat.le_of_mul_le_mul_left hcard hpos
  have heq : f.range = f.ker := Subgroup.eq_of_le_of_card_ge hle hge
  intro q hq hcoc
  have hqk : (⟨q, hq⟩ : Z) ∈ f.ker := by
    rw [MonoidHom.mem_ker, ← Subtype.coe_inj, hf, OneMemClass.coe_one]
    exact hcoc
  rw [← heq] at hqk
  obtain ⟨p, hp⟩ := hqk
  refine ⟨p, p.2, ?_⟩
  have hp' : ((f p : Z) : G) = q := congrArg Subtype.val hp
  rw [hf] at hp'
  rw [← hp', inv_eq_of_mul_eq_one_right (hZ2 p p.2)]

theorem hOneTrivial_sup_of_swap {W₁ W₂ : Subgroup G} {u : G} (hu2 : u * u = 1)
    (hW₁c : ∀ a ∈ W₁, ∀ b ∈ W₁, a * b = b * a) (hW₂c : ∀ a ∈ W₂, ∀ b ∈ W₂, a * b = b * a)
    (hN : W₁ ≤ normalizer (W₂ : Set G)) (h12 : ∀ w ∈ W₁, u * w * u⁻¹ ∈ W₂)
    (h21 : ∀ w ∈ W₂, u * w * u⁻¹ ∈ W₁) (hZ : HOneTrivial u (W₁ ⊓ W₂)) :
    HOneTrivial u (W₁ ⊔ W₂) := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  intro q hq hcoc
  have hq' : q ∈ ((W₁ : Set G) * (W₂ : Set G)) := by
    rw [← coe_mul_of_left_le_normalizer_right W₁ W₂ hN]
    exact hq
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hq'
  set a := u * w₁ * u⁻¹ with ha
  set b := u * w₂ * u⁻¹ with hb
  have haW : a ∈ W₂ := h12 w₁ hw₁
  have hbW : b ∈ W₁ := h21 w₂ hw₂
  have hcoc' : w₁ * w₂ * (a * b) = 1 := by
    rw [ha, hb, ← hcoc]
    group
  have hz1 : w₂ * a = w₁⁻¹ * b⁻¹ := by
    calc w₂ * a = w₁⁻¹ * (w₁ * w₂ * (a * b)) * b⁻¹ := by group
      _ = w₁⁻¹ * b⁻¹ := by rw [hcoc']; group
  have hzZ : w₂ * a ∈ W₁ ⊓ W₂ :=
    mem_inf.2 ⟨hz1 ▸ mul_mem (inv_mem hw₁) (inv_mem hbW), mul_mem hw₂ haW⟩
  have hzc : w₂ * a * (u * (w₂ * a) * u⁻¹) = 1 := by
    have h1 : u * (w₂ * a) * u⁻¹ = b * w₁ := by
      rw [ha, hb, hu']
      calc u * (w₂ * (u * w₁ * u)) * u = u * w₂ * u * w₁ * (u * u) := by group
        _ = u * w₂ * u * w₁ := by rw [hu2, mul_one]
    rw [h1]
    calc w₂ * a * (b * w₁) = w₁⁻¹ * (w₁ * w₂ * (a * b)) * w₁ := by group
      _ = 1 := by rw [hcoc']; group
  obtain ⟨r, hrZ, hr⟩ := hZ _ hzZ hzc
  have hr1 : r ∈ W₁ := (mem_inf.1 hrZ).1
  have hr2 : r ∈ W₂ := (mem_inf.1 hrZ).2
  have hur : u * r * u⁻¹ ∈ W₂ := h12 r hr1
  refine ⟨w₁⁻¹ * r, mem_sup_left (mul_mem (inv_mem hw₁) hr1), ?_⟩
  have hw₂eq : w₂ = (w₂ * a) * a⁻¹ := by group
  have hrw : r * w₁ = w₁ * r := hW₁c r hr1 w₁ hw₁
  have hra : (u * r * u⁻¹) * a⁻¹ = a⁻¹ * (u * r * u⁻¹) := hW₂c _ hur _ (inv_mem haW)
  calc w₁ * w₂ = w₁ * ((w₂ * a) * a⁻¹) := by rw [← hw₂eq]
    _ = w₁ * (r⁻¹ * (u * r * u⁻¹)) * a⁻¹ := by rw [hr]; group
    _ = (w₁ * r⁻¹) * ((u * r * u⁻¹) * a⁻¹) := by group
    _ = (r⁻¹ * w₁) * (a⁻¹ * (u * r * u⁻¹)) := by
        rw [hra]
        congr 1
        calc w₁ * r⁻¹ = r⁻¹ * (r * w₁) * r⁻¹ := by group
          _ = r⁻¹ * (w₁ * r) * r⁻¹ := by rw [hrw]
          _ = r⁻¹ * w₁ := by group
    _ = (w₁⁻¹ * r)⁻¹ * (u * (w₁⁻¹ * r) * u⁻¹) := by rw [ha]; group

theorem exists_mem_centralizer_of_hOneTrivial {X Q : Subgroup G} {H : Type*} [Group H]
    (φ : X →* H) (hQ : ∀ x : X, φ x = 1 ↔ (x : G) ∈ Q) (hQX : Q ≤ X) {u : G} (hu2 : u * u = 1)
    (huX : ∀ x ∈ X, u * x * u⁻¹ ∈ X) (α : H → H)
    (hα : ∀ x : X, φ ⟨u * x * u⁻¹, huX x x.2⟩ = α (φ x)) (hH1 : HOneTrivial u Q)
    (x : X) (hx : α (φ x) = φ x) :
    ∃ y : X, (y : G) ∈ centralizer ({u} : Set G) ∧ φ y = φ x := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hcX : (x : G)⁻¹ * (u * x * u⁻¹) ∈ X := mul_mem (inv_mem x.2) (huX _ x.2)
  have hcQ : (x : G)⁻¹ * (u * x * u⁻¹) ∈ Q := by
    have h1 : (⟨(x : G)⁻¹ * (u * x * u⁻¹), hcX⟩ : X) = x⁻¹ * ⟨u * x * u⁻¹, huX x x.2⟩ := rfl
    refine (hQ ⟨_, hcX⟩).1 ?_
    rw [h1, map_mul, map_inv, hα, hx, inv_mul_cancel]
  have hcoc : (x : G)⁻¹ * (u * x * u⁻¹) * (u * ((x : G)⁻¹ * (u * x * u⁻¹)) * u⁻¹) = 1 := by
    have key : ∀ g : G, u * (u * g) = g := fun g => by rw [← mul_assoc, hu2, one_mul]
    rw [hu']
    simp only [mul_assoc, key, mul_inv_cancel_left, inv_mul_cancel_left, hu2]
  obtain ⟨p, hpQ, hp⟩ := hH1 _ hcQ hcoc
  have hpX : p ∈ X := hQX hpQ
  refine ⟨x * ⟨p, hpX⟩⁻¹, mem_centralizer_singleton_iff.2 ?_, ?_⟩
  · have h2 : u * x * u⁻¹ = (x : G) * (p⁻¹ * (u * p * u⁻¹)) := by
      rw [← hp]
      group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    symm
    calc u * (x * p⁻¹) = (u * x * u⁻¹) * (u * p * u⁻¹)⁻¹ * u := by group
      _ = (x : G) * p⁻¹ * u := by rw [h2]; group
  · rw [map_mul, map_inv, (hQ ⟨p, hpX⟩).2 hpQ, inv_one, mul_one]

theorem card_eqLocus_dvd_card_centralizer {X Q : Subgroup G} {H : Type*} [Group H]
    (φ : X →* H) (hφ : Function.Surjective φ) (hQ : ∀ x : X, φ x = 1 ↔ (x : G) ∈ Q)
    (hQX : Q ≤ X) {u : G} (hu2 : u * u = 1) (huX : ∀ x ∈ X, u * x * u⁻¹ ∈ X) (α : H →* H)
    (hα : ∀ x : X, φ ⟨u * x * u⁻¹, huX x x.2⟩ = α (φ x)) (hH1 : HOneTrivial u Q) :
    Nat.card (α.eqLocus (MonoidHom.id H)) ∣ Nat.card (centralizer ({u} : Set G)) := by
  let ψ : (X ⊓ centralizer ({u} : Set G) : Subgroup G) →* H :=
    φ.comp (Subgroup.inclusion inf_le_left)
  have hψ : ψ.range = α.eqLocus (MonoidHom.id H) := by
    ext h
    constructor
    · rintro ⟨c, rfl⟩
      have hcu : u * c * u⁻¹ = c := by
        rw [← mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).2]
        group
      change α (φ _) = φ _
      rw [← hα]
      congr 1
      exact Subtype.ext hcu
    · intro hh
      obtain ⟨x, rfl⟩ := hφ h
      obtain ⟨y, hyC, hy⟩ := exists_mem_centralizer_of_hOneTrivial φ hQ hQX hu2 huX α hα hH1 x hh
      exact ⟨⟨y, mem_inf.2 ⟨y.2, hyC⟩⟩, hy⟩
  rw [← hψ]
  exact (Subgroup.card_range_dvd ψ).trans (Subgroup.card_dvd_of_le inf_le_right)

theorem involutive_of_surjective_of_conj {X : Subgroup G} {H : Type*} [Group H] (φ : X →* H)
    (hφ : Function.Surjective φ) {u : G} (hu2 : u * u = 1) (huX : ∀ x ∈ X, u * x * u⁻¹ ∈ X)
    (β : H → H) (hβ : ∀ x : X, φ ⟨u * x * u⁻¹, huX x x.2⟩ = β (φ x)) (y : H) :
    β (β y) = y := by
  obtain ⟨x, rfl⟩ := hφ y
  have hx2 : u * (u * x * u⁻¹) * u⁻¹ ∈ X := huX _ (huX x x.2)
  have h1 : (⟨u * (u * x * u⁻¹) * u⁻¹, hx2⟩ : X) = x := by
    apply Subtype.ext
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    show u * (u * (x : G) * u⁻¹) * u⁻¹ = x
    rw [hu']
    calc u * (u * (x : G) * u) * u = (u * u) * x * (u * u) := by group
      _ = x := by rw [hu2]; group
  rw [← hβ x, ← hβ ⟨u * x * u⁻¹, huX x x.2⟩]
  exact congrArg φ h1

end Cohom

end CFSG.SeitzReduction.LinearPilot
