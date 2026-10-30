module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem q14_ncard_modEq_fixed {rho : G} (hρ : rho ^ 3 = 1) {Ω : Set G}
    (hΩ : ∀ x ∈ Ω, rho * x * rho⁻¹ ∈ Ω) :
    Ω.ncard ≡ {x | x ∈ Ω ∧ rho * x * rho⁻¹ = x}.ncard [MOD 3] := by
  classical
  letI : Fintype ↥Ω := Fintype.ofFinite ↥Ω
  let f : Function.End ↥Ω := fun x => ⟨rho * (x : G) * rho⁻¹, hΩ x x.2⟩
  have hr3 : rho * rho * rho = 1 := by simpa [pow_three'] using hρ
  have hf : f ^ 3 ^ 1 = 1 := by
    rw [pow_one, pow_succ, pow_succ, pow_one]
    funext x
    apply Subtype.ext
    show rho * (rho * (rho * (x : G) * rho⁻¹) * rho⁻¹) * rho⁻¹ = (x : G)
    calc rho * (rho * (rho * (x : G) * rho⁻¹) * rho⁻¹) * rho⁻¹
        = (rho * rho * rho) * (x : G) * (rho * rho * rho)⁻¹ := by group
      _ = (x : G) := by rw [hr3]; group
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  have hset : Subtype.val '' Function.fixedPoints f =
      {x : G | x ∈ Ω ∧ rho * x * rho⁻¹ = x} := by
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have hy' : f y = y := hy
      exact congrArg Subtype.val hy'
    · rintro ⟨hxΩ, hx⟩
      exact ⟨⟨x, hxΩ⟩, Subtype.ext hx, rfl⟩
  have h2 : Ω.ncard = Fintype.card ↥Ω := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  have h1 : Fintype.card (Function.fixedPoints f) =
      {x : G | x ∈ Ω ∧ rho * x * rho⁻¹ = x}.ncard := by
    rw [← hset, Set.ncard_image_of_injective _ Subtype.coe_injective]
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rw [h2, ← h1]
  exact hmod

theorem q14_exists_fixed_coset {rho w : G} {N : Subgroup G} (hρ : rho ^ 3 = 1)
    (hN : ∀ n ∈ N, rho * n * rho⁻¹ ∈ N) (hcard : ¬ 3 ∣ Nat.card N)
    (hw : rho * w * rho⁻¹ * w⁻¹ ∈ N) :
    ∃ x : G, x * w⁻¹ ∈ N ∧ rho * x * rho⁻¹ = x := by
  classical
  by_contra h
  push Not at h
  let Ω : Set G := {x : G | x * w⁻¹ ∈ N}
  have hΩ : ∀ x ∈ Ω, rho * x * rho⁻¹ ∈ Ω := by
    intro x hx
    have h1 : rho * (x * w⁻¹) * rho⁻¹ ∈ N := hN (x * w⁻¹) hx
    have h2 : rho * x * rho⁻¹ * w⁻¹ =
        (rho * (x * w⁻¹) * rho⁻¹) * (rho * w * rho⁻¹ * w⁻¹) := by group
    show rho * x * rho⁻¹ * w⁻¹ ∈ N
    rw [h2]
    exact mul_mem h1 hw
  have hmod := q14_ncard_modEq_fixed hρ hΩ
  have hemp : {x : G | x ∈ Ω ∧ rho * x * rho⁻¹ = x} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact h x hx.1 hx.2
  rw [hemp] at hmod
  simp only [Set.ncard_empty] at hmod
  rw [Nat.modEq_zero_iff_dvd] at hmod
  let e : ↥Ω ≃ N :=
    { toFun := fun x => ⟨x.1 * w⁻¹, x.2⟩
      invFun := fun n => ⟨n.1 * w, by
        show (n : G) * w * w⁻¹ ∈ N
        rw [mul_assoc, mul_inv_cancel, mul_one]
        exact n.2⟩
      left_inv := fun x => by apply Subtype.ext; group
      right_inv := fun n => by apply Subtype.ext; group }
  have hcardΩ : Ω.ncard = Nat.card N := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr e
  rw [hcardΩ] at hmod
  exact hcard hmod

theorem q14_card_mod_three {rho : G} {D : Subgroup G} (hρ : rho ^ 3 = 1)
    (hD : ∀ d ∈ D, rho * d * rho⁻¹ ∈ D) (hfix : ∀ d ∈ D, rho * d * rho⁻¹ = d → d = 1) :
    Nat.card D % 3 = 1 := by
  classical
  have hΩ : ∀ x ∈ (D : Set G), rho * x * rho⁻¹ ∈ (D : Set G) := fun x hx => hD x hx
  have hmod := q14_ncard_modEq_fixed hρ hΩ
  have hfixset : {x : G | x ∈ (D : Set G) ∧ rho * x * rho⁻¹ = x} = {1} := by
    ext x
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hxD, hx⟩
      exact hfix x hxD hx
    · rintro rfl
      exact ⟨D.one_mem, by group⟩
  rw [hfixset] at hmod
  simp only [Set.ncard_singleton] at hmod
  have h : Nat.card D ≡ 1 [MOD 3] := hmod
  rw [Nat.ModEq] at h
  norm_num at h
  exact h

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
