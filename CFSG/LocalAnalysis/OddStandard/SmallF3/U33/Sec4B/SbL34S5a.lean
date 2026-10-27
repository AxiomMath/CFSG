module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup

variable {G : Type*} [Group G] [Finite G]

private theorem card_modEq_fixed_perm {α : Type*} [Finite α] (σ : Equiv.Perm α)
    (h3 : σ ^ 3 = 1) :
    Nat.card α ≡ (Function.fixedPoints σ).ncard [MOD 3] := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype α := Fintype.ofFinite α
  let f : Function.End α := ⇑σ
  have hpow : ∀ k : ℕ, f ^ k = (⇑(σ ^ k) : Function.End α) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      rfl
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) (by
    rw [pow_one, hpow, h3]; rfl)
  have e : Nat.card α = Fintype.card α := Nat.card_eq_fintype_card
  have e2 : (Function.fixedPoints σ).ncard = Fintype.card ↑(Function.fixedPoints f) := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rw [e, e2]
  exact h

theorem card_modEq_fixed (ρ : G) (hρ3 : ρ * ρ * ρ = 1) (C : Set G)
    (hC : ∀ x ∈ C, ρ * x * ρ⁻¹ ∈ C) :
    C.ncard ≡ {x ∈ C | ρ * x * ρ⁻¹ = x}.ncard [MOD 3] := by
  classical
  haveI : Fintype ↥C := Fintype.ofFinite ↥C
  let f : ↥C → ↥C := fun x => ⟨ρ * x * ρ⁻¹, hC x x.2⟩
  have hfinj : Function.Injective f := by
    intro x y h
    have h' : ρ * (x : G) * ρ⁻¹ = ρ * (y : G) * ρ⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  let σ : Equiv.Perm ↥C := Equiv.ofBijective f ⟨hfinj, Finite.surjective_of_injective hfinj⟩
  have hσf : ∀ x : ↥C, σ x = f x := fun x => rfl
  have hσ3 : σ ^ 3 = 1 := by
    ext x
    have hcalc : ρ * (ρ * (ρ * (x : G) * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ = (x : G) := by
      have k1 : ρ * (ρ * (ρ * (x : G) * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ =
          (ρ * ρ * ρ) * (x : G) * (ρ * ρ * ρ)⁻¹ := by group
      rw [k1, hρ3, inv_one, mul_one, one_mul]
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, hσf]
    exact hcalc
  have hmod := card_modEq_fixed_perm σ hσ3
  have hcardfix : (Function.fixedPoints σ).ncard = {x ∈ C | ρ * x * ρ⁻¹ = x}.ncard := by
    refine Set.ncard_congr' ?_
    exact
      { toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, Subtype.ext y.2.2⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun y => Subtype.ext rfl }
  rw [Nat.card_coe_set_eq C] at hmod
  rw [hcardfix] at hmod
  exact hmod

theorem card_modEq_one_of_conj_fpf (B : Subgroup G) (ρ : G) (hρ3 : ρ * ρ * ρ = 1)
    (hρB : ∀ b ∈ B, ρ * b * ρ⁻¹ ∈ B) (hfix : ∀ b ∈ B, ρ * b = b * ρ → b = 1) :
    Nat.card B ≡ 1 [MOD 3] := by
  have h := card_modEq_fixed ρ hρ3 (B : Set G) hρB
  have hset : {x ∈ (B : Set G) | ρ * x * ρ⁻¹ = x} = {1} := by
    ext x
    constructor
    · rintro ⟨hxB, hx⟩
      rw [Set.mem_singleton_iff]
      have hcomm : ρ * x = x * ρ := by
        calc ρ * x = ρ * x * ρ⁻¹ * ρ := by group
          _ = x * ρ := by rw [hx]
      exact hfix x hxB hcomm
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨B.one_mem, by group⟩
  rw [hset, Set.ncard_singleton] at h
  rwa [← Nat.card_coe_set_eq (B : Set G)] at h

theorem card_cases_of_conj_fpf (K : Subgroup G) (ρ : G) (hρ3 : ρ * ρ * ρ = 1)
    (hρK : ∀ k ∈ K, ρ * k * ρ⁻¹ ∈ K) (hfix : ∀ k ∈ K, ρ * k = k * ρ → k = 1)
    (hdvd : Nat.card K ∣ 2 ^ 6) :
    Nat.card K = 1 ∨ Nat.card K = 4 ∨ Nat.card K = 16 ∨ Nat.card K = 64 := by
  have hmod : Nat.card K ≡ 1 [MOD 3] :=
    card_modEq_one_of_conj_fpf K ρ hρ3 hρK hfix
  obtain ⟨k, hk_le, hk_eq⟩ :=
    (Nat.dvd_prime_pow (p := 2) (m := 6) Nat.prime_two).mp hdvd
  rw [hk_eq] at hmod ⊢
  interval_cases k <;> simp_all [Nat.ModEq]

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
