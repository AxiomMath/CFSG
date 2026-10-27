module


public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.RingTheory.PrincipalIdealDomain

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.PrimeOrbitEquivariantSection

theorem exists_section {X Y : Type*} (π : Y → X) (hπ : Function.Surjective π)
    (σ : Equiv.Perm X) (τ : Equiv.Perm Y) (r : ℕ) (hr : r.Prime) (hσ : σ ^ r = 1)
    (hτ : τ ^ r = 1) (hπστ : ∀ y, π (τ y) = σ (π y)) (x0 : X)
    (hfix : ∀ x, σ x = x ↔ x = x0) (y0 : Y) (hy0 : π y0 = x0) (hτy0 : τ y0 = y0) :
    ∃ s : X → Y, (∀ x, π (s x) = x) ∧ (∀ x, s (σ x) = τ (s x)) ∧ s x0 = y0 := by
  have pi_zpow (π : Y → X) (σ : Equiv.Perm X) (τ : Equiv.Perm Y)
      (hπ : ∀ y, π (τ y) = σ (π y)) (k : ℤ) (y : Y) : π ((τ ^ k) y) = (σ ^ k) (π y) := by
    induction k using Int.induction_on generalizing y with
    | zero => simp
    | succ n ih =>
      rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hπ, zpow_add_one, Equiv.Perm.mul_apply]
    | pred n ih =>
      rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
      have h1 : π (τ⁻¹ y) = σ⁻¹ (π y) := by
        apply (Equiv.Perm.eq_inv_iff_eq).2
        rw [← hπ]; simp
      rw [h1, zpow_sub_one, Equiv.Perm.mul_apply]
  have dvd_of_fix (σ : Equiv.Perm X) (r : ℕ) (hr : r.Prime) (hσ : σ ^ r = 1)
      (x0 : X) (hfix : ∀ x, σ x = x ↔ x = x0) (z : X) (hz : z ≠ x0) (k : ℤ)
      (hk : (σ ^ k) z = z) : (r : ℤ) ∣ k := by
    by_contra hnd
    have hcop : IsCoprime (r : ℤ) k :=
      (Nat.prime_iff_prime_int.1 hr).coprime_iff_not_dvd.2 hnd
    obtain ⟨a, b, hab⟩ := hcop
    have hr1 : σ ^ (r : ℤ) = 1 := by rw [zpow_natCast, hσ]
    have h1 : (σ ^ (1 : ℤ)) z = z := by
      rw [← hab, zpow_add, Equiv.Perm.mul_apply, mul_comm a, zpow_mul, hr1, one_zpow,
        mul_comm b, zpow_mul]
      simpa using Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hk b
    exact hz ((hfix z).1 (by simpa using h1))
  classical
  let S : Setoid X := MulAction.orbitRel (Subgroup.zpowers σ) X
  have horb : ∀ x y, S x y ↔ ∃ k : ℤ, (σ ^ k) y = x := by
    intro x y
    show MulAction.orbitRel (Subgroup.zpowers σ) X x y ↔ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨⟨_, k, rfl⟩, h⟩
      exact ⟨k, h⟩
    · rintro ⟨k, h⟩
      exact ⟨⟨σ ^ k, k, rfl⟩, h⟩
  let rep : X → X := fun x => Quotient.out (Quotient.mk S x)
  have hrep1 : ∀ x, ∃ k : ℤ, (σ ^ k) (rep x) = x := fun x =>
    (horb x (rep x)).1 (Setoid.symm (Quotient.mk_out x))
  have hrep2 : ∀ x, rep (σ x) = rep x := by
    intro x
    have : (Quotient.mk S (σ x)) = Quotient.mk S x :=
      Quotient.sound ((horb _ _).2 ⟨1, by simp⟩)
    simp only [rep, this]
  have hrep3 : ∀ x, x ≠ x0 → rep x ≠ x0 := by
    intro x hx h
    obtain ⟨k, hk⟩ := hrep1 x
    rw [h] at hk
    exact hx (by rw [← hk]; exact (Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self
      ((hfix x0).2 rfl) k))
  let yrep : X → Y := Function.surjInv hπ
  have hyrep : ∀ x, π (yrep x) = x := Function.surjInv_eq hπ
  let kk : X → ℤ := fun x => Classical.choose (hrep1 x)
  have hkk : ∀ x, (σ ^ kk x) (rep x) = x := fun x => Classical.choose_spec (hrep1 x)
  have hτ' : τ ^ (r : ℤ) = 1 := by rw [zpow_natCast, hτ]
  refine ⟨fun x => if x = x0 then y0 else (τ ^ kk x) (yrep (rep x)), ?_, ?_, by simp⟩
  · intro x
    by_cases hx : x = x0
    · simp [hx, hy0]
    · simp only [hx, if_false]
      rw [pi_zpow π σ τ hπστ, hyrep, hkk]
  · intro x
    by_cases hx : x = x0
    · subst hx
      have : σ x = x := (hfix x).2 rfl
      simp [this, hτy0]
    · have hσx : σ x ≠ x0 := by
        intro h
        apply hx
        have : σ x = σ x0 := by rw [h, (hfix x0).2 rfl]
        exact σ.injective this
      simp only [hx, hσx, if_false, hrep2]
      have hz := hrep3 x hx
      have hd : (r : ℤ) ∣ kk (σ x) - (kk x + 1) := by
        apply dvd_of_fix σ r hr hσ x0 hfix _ hz
        have h1 := hkk (σ x)
        rw [hrep2] at h1
        have h2 : (σ ^ (kk x + 1)) (rep x) = σ x := by
          rw [add_comm, zpow_add, Equiv.Perm.mul_apply, hkk, zpow_one]
        rw [sub_eq_neg_add, zpow_add, Equiv.Perm.mul_apply, h1, ← h2]
        simp [← Equiv.Perm.mul_apply, ← zpow_add]
      obtain ⟨m, hm⟩ := hd
      have : kk (σ x) = (kk x + 1) + r * m := by omega
      rw [this, zpow_add τ (kk x + 1) (r * m), zpow_mul, hτ', one_zpow, mul_one,
        add_comm (kk x) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply]

end CFSG.GroupTheory.CoprimeActionSupport.PrimeOrbitEquivariantSection
