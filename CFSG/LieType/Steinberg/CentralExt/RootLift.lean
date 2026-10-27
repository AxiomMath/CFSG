module

public import CFSG.LieType.Steinberg.CentralExt.TorusLift

public section

open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.RootLift

section Generic

variable {E : Type*} [Group E] {k : Type*} [Field k]

theorem eq_one_of_add_of_smul {ρ : k → E} (hadd : ∀ s s', ρ (s + s') = ρ s * ρ s')
    {a : k} (ha : a ≠ 1) (hinv : ∀ s, ρ (a * s) = ρ s) (s : k) : ρ s = 1 := by
  have h1 : ∀ s, ρ ((a - 1) * s) = 1 := fun s => by
    have := hadd ((a - 1) * s) s
    rw [show (a - 1) * s + s = a * s by ring, hinv] at this
    exact (mul_eq_right.1 this.symm)
  have := h1 ((a - 1)⁻¹ * s)
  rwa [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.2 ha), one_mul] at this

theorem commutatorElement_mul_left_conj (a b c : E) :
    ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]
  group

theorem mul_mul_central {c : E} (hc : ∀ g, g * c = c * g) (a b : E) : a * c * b = a * b * c := by
  rw [mul_assoc, ← hc b, ← mul_assoc]

end Generic

section Lift

variable {E K : Type*} [Group E] [Group K] {π : E →* K} (hcen : π.ker ≤ Subgroup.center E)
  {k : Type*} [Field k]
include hcen

theorem commute_lifts {x y : k → K} {X Y : k → E} (hX : ∀ s s', X (s + s') = X s * X s')
    (hπX : ∀ s, π (X s) = x s) (hπY : ∀ t, π (Y t) = y t) (hxy : ∀ s t, x s * y t = y t * x s)
    {h : E} {a : k} (ha : a ≠ 1) (hhX : ∀ s, h * X s * h⁻¹ = X (a * s))
    (hhY : ∀ t, h * Y t * h⁻¹ = Y t) (s t : k) : X s * Y t = Y t * X s := by
  set ρ : k → E := fun s => ⁅X s, Y t⁆ with hρ
  have hker : ∀ s, ρ s ∈ π.ker := fun s => by
    rw [MonoidHom.mem_ker, hρ, map_commutatorElement, hπX, hπY,
      commutatorElement_eq_one_iff_mul_comm, hxy]
  have hadd : ∀ s s', ρ (s + s') = ρ s * ρ s' := fun s s' => by
    simp only [hρ, hX]
    rw [TorusLift.commutatorElement_mul_left_of_central (hcen (hker s'))]
  have hinv : ∀ s, ρ (a * s) = ρ s := fun s => by
    have e : h * ρ s * h⁻¹ = ρ (a * s) := by
      simp only [hρ]
      rw [conjugate_commutatorElement, hhX, hhY]
    rw [← e, (Subgroup.mem_center_iff.1 (hcen (hker s)) h), mul_inv_cancel_right]
  have := eq_one_of_add_of_smul hadd ha hinv s
  rwa [hρ, commutatorElement_eq_one_iff_mul_comm] at this

theorem commutator_lifts_eq {x y z : k → K} {X Y Z : k → E} (hX : ∀ s s', X (s + s') = X s * X s')
    (hZ : ∀ r r', Z (r + r') = Z r * Z r') (hπX : ∀ s, π (X s) = x s)
    (hπY : ∀ t, π (Y t) = y t) (hπZ : ∀ r, π (Z r) = z r) {C : k}
    (hxyz : ∀ s t, ⁅x s, y t⁆ = z (C * s * t)) (hXZ : ∀ s r, X s * Z r = Z r * X s)
    {h : E} {a : k} (ha : a ≠ 1) (hhX : ∀ s, h * X s * h⁻¹ = X (a * s))
    (hhY : ∀ t, h * Y t * h⁻¹ = Y t) (hhZ : ∀ r, h * Z r * h⁻¹ = Z (a * r)) (s t : k) :
    ⁅X s, Y t⁆ = Z (C * s * t) := by
  set ρ : k → E := fun s => (Z (C * s * t))⁻¹ * ⁅X s, Y t⁆ with hρ
  have hker : ∀ s, ρ s ∈ π.ker := fun s => by
    rw [MonoidHom.mem_ker, hρ, map_mul, map_inv, map_commutatorElement, hπX, hπY, hπZ, hxyz,
      inv_mul_cancel]
  have hc : ∀ s g, g * ρ s = ρ s * g := fun s g =>
    (Subgroup.mem_center_iff.1 (hcen (hker s))) g
  have hdec : ∀ s, ⁅X s, Y t⁆ = Z (C * s * t) * ρ s := fun s => by
    simp only [hρ]
    group
  have hZc : ∀ r r', Z r * Z r' = Z r' * Z r := fun r r' => by
    rw [← hZ, ← hZ, add_comm]
  have hadd : ∀ s s', ρ (s + s') = ρ s * ρ s' := fun s s' => by
    have e0 : X s * (Z (C * s' * t) * ρ s') * (X s)⁻¹ = Z (C * s' * t) * ρ s' := by
      rw [← mul_assoc, mul_mul_central (hc s'), hXZ, mul_inv_cancel_right]
    have e1 : ⁅X (s + s'), Y t⁆ = Z (C * s * t) * Z (C * s' * t) * (ρ s * ρ s') := by
      rw [hX, commutatorElement_mul_left_conj, hdec s', hdec s, e0, ← mul_assoc,
        mul_mul_central (hc s'), hZc, mul_assoc _ (ρ s'), ← hc s' (ρ s)]
    have e3 : ⁅X (s + s'), Y t⁆ = Z (C * s * t) * Z (C * s' * t) * ρ (s + s') := by
      rw [hdec, ← hZ, show C * (s + s') * t = C * s * t + C * s' * t by ring]
    exact mul_left_cancel (e3.symm.trans e1)
  have hinv : ∀ s, ρ (a * s) = ρ s := fun s => by
    have e1 : h * ⁅X s, Y t⁆ * h⁻¹ = ⁅X (a * s), Y t⁆ := by
      rw [conjugate_commutatorElement, hhX, hhY]
    rw [hdec s, hdec (a * s), ← mul_assoc, mul_mul_central (hc s), hhZ,
      show a * (C * s * t) = C * (a * s) * t by ring] at e1
    exact (mul_left_cancel e1).symm
  have := eq_one_of_add_of_smul hadd ha hinv s
  rw [hdec, this, mul_one]

end Lift

end CFSG.LieType.Steinberg.CentralExt.RootLift
