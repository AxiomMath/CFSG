module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem exists_ne_one_commute_of_normalizes {p : ℕ} [Fact p.Prime] {P O : Subgroup G}
    [Finite O] (hP : IsPGroup p P) (hO : IsPGroup p O) (hO1 : O ≠ ⊥)
    (hn : ∀ g ∈ P, ∀ o ∈ O, g * o * g⁻¹ ∈ O) : ∃ o ∈ O, o ≠ 1 ∧ ∀ g ∈ P, g * o = o * g := by
  let _ : MulAction P O :=
    { smul := fun g o => ⟨(g : G) * o * (g : G)⁻¹, hn g g.2 o o.2⟩
      one_smul := fun o => Subtype.ext (by
        change ((1 : P) : G) * (o : G) * ((1 : P) : G)⁻¹ = o
        rw [Subgroup.coe_one, one_mul, inv_one, mul_one])
      mul_smul := fun a b o => Subtype.ext (by
        change ((a * b : P) : G) * (o : G) * ((a * b : P) : G)⁻¹ =
          (a : G) * ((b : G) * o * (b : G)⁻¹) * (a : G)⁻¹
        rw [Subgroup.coe_mul, mul_inv_rev]
        simp only [mul_assoc]) }
  have h1 : (1 : O) ∈ MulAction.fixedPoints P O := fun g => Subtype.ext (by
    change (g : G) * 1 * (g : G)⁻¹ = 1
    rw [mul_one, mul_inv_cancel])
  have hdvd : p ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := hO.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hO1 ((Subgroup.card_eq_one).mp hk)
    rw [hk]
    exact dvd_pow_self p hk0
  obtain ⟨b, hb, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point O hdvd h1
  refine ⟨b, b.2, fun h => hne (Subtype.ext h.symm), fun g hg => ?_⟩
  have e : (g : G) * b * (g : G)⁻¹ = b := congrArg Subtype.val (hb ⟨g, hg⟩)
  calc g * (b : G) = g * b * g⁻¹ * g := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = b * g := by rw [e]

end CFSG.GroupTheory
