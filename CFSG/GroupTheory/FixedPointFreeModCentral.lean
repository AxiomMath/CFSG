module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

def fixedModSubgroup (Q Z : Subgroup G) (k : G)
    (hQZ : Q ≤ Subgroup.normalizer (Z : Set G)) : Subgroup G where
  carrier := {x | x ∈ Q ∧ k * x * k⁻¹ * x⁻¹ ∈ Z}
  one_mem' := by
    refine ⟨Q.one_mem, ?_⟩
    simp
  mul_mem' := by
    rintro x y ⟨hxQ, hxZ⟩ ⟨hyQ, hyZ⟩
    refine ⟨Q.mul_mem hxQ hyQ, ?_⟩
    have hxN : x ∈ Subgroup.normalizer (Z : Set G) := hQZ hxQ
    have hconj : x * (k * y * k⁻¹ * y⁻¹) * x⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp hxN _).mp hyZ
    have hmul : (k * x * k⁻¹ * x⁻¹) * (x * (k * y * k⁻¹ * y⁻¹) * x⁻¹) ∈ Z :=
      Z.mul_mem hxZ hconj
    have h : (k * x * k⁻¹ * x⁻¹) * (x * (k * y * k⁻¹ * y⁻¹) * x⁻¹) =
        k * (x * y) * k⁻¹ * (x * y)⁻¹ := by
      group
    rwa [h] at hmul
  inv_mem' := by
    rintro x ⟨hxQ, hxZ⟩
    refine ⟨Q.inv_mem hxQ, ?_⟩
    rw [inv_inv]
    have hxN : x⁻¹ ∈ Subgroup.normalizer (Z : Set G) :=
      (Subgroup.normalizer (Z : Set G)).inv_mem (hQZ hxQ)
    have hconj : x⁻¹ * (k * x * k⁻¹ * x⁻¹)⁻¹ * x ∈ Z := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp hxN _).mp (Z.inv_mem hxZ)
    have h : x⁻¹ * (k * x * k⁻¹ * x⁻¹)⁻¹ * x = k * x⁻¹ * k⁻¹ * x := by
      group
    rwa [h] at hconj

@[simp] theorem mem_fixedModSubgroup {Q Z : Subgroup G} {k x : G}
    {hQZ : Q ≤ Subgroup.normalizer (Z : Set G)} :
    x ∈ fixedModSubgroup Q Z k hQZ ↔ x ∈ Q ∧ k * x * k⁻¹ * x⁻¹ ∈ Z :=
  Iff.rfl

theorem le_fixedModSubgroup {Q Z : Subgroup G} {k : G}
    (hQZ : Q ≤ Subgroup.normalizer (Z : Set G)) (hZQ : Z ≤ Q)
    (hkZ : k ∈ Subgroup.normalizer (Z : Set G)) : Z ≤ fixedModSubgroup Q Z k hQZ := by
  intro z hz
  rw [mem_fixedModSubgroup]
  refine ⟨hZQ hz, ?_⟩
  have h1 : k * z * k⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hkZ z).mp hz
  exact Z.mul_mem h1 (Z.inv_mem hz)

theorem conj_conj_mul_inv_mem_of_pow_three_eq_one {Q Z : Subgroup G} {k x : G}
    (hk : k ^ 3 = 1) (hkQ : ∀ q ∈ Q, k * q * k⁻¹ ∈ Q)
    (hZc : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z) (hsq : ∀ q ∈ Q, q ^ 2 ∈ Z)
    (hcm : ∀ q ∈ Q, ∀ r ∈ Q, ⁅q, r⁆ ∈ Z)
    (hfix : ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ Z → q ∈ Z) (hx : x ∈ Q) :
    k * (k * x * k⁻¹) * k⁻¹ * (x * (k * x * k⁻¹))⁻¹ ∈ Z := by
  let y : G := k * x * k⁻¹
  let w : G := k * y * k⁻¹
  let p : G := x * y * w
  have hyQ : y ∈ Q := hkQ x hx
  have hwQ : w ∈ Q := hkQ y hyQ
  have hxyQ : x * y ∈ Q := Q.mul_mem hx hyQ
  have hpQ : p ∈ Q := Q.mul_mem hxyQ hwQ
  have hkw : k * w * k⁻¹ = x := by
    have h : k * w * k⁻¹ = (k * k * k) * x * (k * k * k)⁻¹ := by
      simp only [w, y]
      group
    rw [h, show k * k * k = k ^ 3 by simp [pow_succ, pow_two, mul_assoc], hk]
    simp
  have hkp : k * p * k⁻¹ = y * w * x := by
    have h : k * p * k⁻¹ =
        (k * x * k⁻¹) * (k * y * k⁻¹) * (k * w * k⁻¹) := by
      simp only [p]
      group
    rw [h, hkw]
  have hcomm : k * p * k⁻¹ * p⁻¹ = ⁅y * w, x⁆ := by
    rw [hkp, commutatorElement_def]
    simp only [p]
    group
  have hpZ : p ∈ Z :=
    hfix p hpQ (by rw [hcomm]; exact hcm (y * w) (Q.mul_mem hyQ hwQ) x hx)
  change w * (x * y)⁻¹ ∈ Z
  have hzQ : (x * y)⁻¹ ∈ Q := Q.inv_mem hxyQ
  have hzp : (x * y)⁻¹ * p = p * (x * y)⁻¹ := (hZc p hpZ _ hzQ).symm
  have hw_eq : w = (x * y)⁻¹ * p := by
    simp only [p]
    group
  have hz2 : (x * y)⁻¹ * (x * y)⁻¹ ∈ Z := by
    simpa [pow_two] using hsq _ hzQ
  rw [hw_eq]
  have heq : (x * y)⁻¹ * p * (x * y)⁻¹ =
      p * ((x * y)⁻¹ * (x * y)⁻¹) := by
    rw [hzp]
    group
  rw [heq]
  exact Z.mul_mem hpZ hz2

end CFSG.GroupTheory
