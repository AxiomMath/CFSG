module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.S56

open Subgroup

variable {G : Type*} [Group G]

private theorem exists_fixedPoint_of_iterate_five {α : Type*} [Finite α] {f : α → α}
    (hf : ∀ a, f^[5] a = a) (hα : ¬ 5 ∣ Nat.card α) : ∃ a, f a = a := by
  classical
  haveI := Fintype.ofFinite α
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let σ : Equiv.Perm α :=
    { toFun := f
      invFun := f^[4]
      left_inv := fun a => (Function.iterate_succ_apply f 4 a).symm.trans (hf a)
      right_inv := fun a => (Function.iterate_succ_apply' f 4 a).symm.trans (hf a) }
  have hσ : σ ^ 5 ^ 1 = 1 := by
    ext a
    rw [Equiv.Perm.coe_pow]
    exact hf a
  rw [Nat.card_eq_fintype_card] at hα
  exact Equiv.Perm.exists_fixed_point_of_prime (p := 5) (n := 1) hα hσ

private theorem iterate_conj_apply (x g : G) (n : ℕ) :
    (fun w : G => x * w * x⁻¹)^[n] g = x ^ n * g * (x ^ n)⁻¹ := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    group

theorem exists_fixed_point_of_conj_stable [Finite G] {x : G}
    (hx : orderOf x = 5) {Ω : Set G} (hΩ : ∀ w ∈ Ω, x * w * x⁻¹ ∈ Ω) (_hne : Ω.Nonempty)
    (hcard : ¬ 5 ∣ Nat.card Ω) : ∃ w ∈ Ω, x * w * x⁻¹ = w := by
  have hx5 : x ^ 5 = 1 := by simpa [hx] using pow_orderOf_eq_one x
  let f : Ω → Ω := fun w => ⟨x * w * x⁻¹, hΩ w w.2⟩
  have hsc : Function.Semiconj (Subtype.val : Ω → G) f (fun w : G => x * w * x⁻¹) :=
    fun w => rfl
  have hf5 : ∀ w, f^[5] w = w := by
    intro w
    apply Subtype.ext
    rw [hsc.iterate_right 5 w, iterate_conj_apply, hx5]
    simp
  obtain ⟨w, hw⟩ := exists_fixedPoint_of_iterate_five hf5 hcard
  exact ⟨w, w.2, congrArg Subtype.val hw⟩

theorem exists_fixed_point_of_conj_stable_coset [Finite G] {x : G} (hx : orderOf x = 5)
    {E : Subgroup G} (hxE : x ∈ normalizer (E : Set G)) {z₁ : G}
    (hz₁ : z₁⁻¹ * (x * z₁ * x⁻¹) ∈ E) (hcard : ¬ 5 ∣ Nat.card E) :
    ∃ e ∈ E, x * (z₁ * e) * x⁻¹ = z₁ * e := by
  have hΩ : ∀ w ∈ (fun e => z₁ * e) '' (E : Set G),
      x * w * x⁻¹ ∈ (fun e => z₁ * e) '' (E : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    refine ⟨z₁⁻¹ * (x * z₁ * x⁻¹) * (x * e * x⁻¹),
      E.mul_mem hz₁ ((mem_normalizer_iff.1 hxE e).1 he), ?_⟩
    show z₁ * (z₁⁻¹ * (x * z₁ * x⁻¹) * (x * e * x⁻¹)) = x * (z₁ * e) * x⁻¹
    group
  have hne : ((fun e => z₁ * e) '' (E : Set G)).Nonempty := ⟨z₁ * 1, 1, E.one_mem, rfl⟩
  have hc : Nat.card ((fun e => z₁ * e) '' (E : Set G)) = Nat.card E :=
    Nat.card_image_of_injective (mul_right_injective z₁) (E : Set G)
  obtain ⟨_, ⟨e, he, rfl⟩, hfix⟩ :=
    exists_fixed_point_of_conj_stable hx hΩ hne (by rw [hc]; exact hcard)
  exact ⟨e, he, hfix⟩

end CFSG.LocalAnalysis.EvenBN.Tits.S56
