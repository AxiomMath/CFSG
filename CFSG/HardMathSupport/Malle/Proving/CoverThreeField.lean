module

public import CFSG.CharacterTheory.Semidihedral.FixedFieldData
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem cube_add_one_mod_nine_of_mod_three (m : ℕ) (h : (m ^ 3 + 1) % 3 = 0) :
    (m ^ 3 + 1) % 9 = 0 := by
  have h9 : m ^ 3 % 9 = (m % 9) ^ 3 % 9 := Nat.pow_mod m 3 9
  have h3 : (m % 3) ^ 3 % 3 = 2 := by
    rw [← Nat.pow_mod]
    generalize m ^ 3 = x at h ⊢
    omega
  obtain ⟨r, hr⟩ : ∃ r, m % 9 = r := ⟨_, rfl⟩
  have hr9 : r < 9 := by omega
  have hr3 : m % 3 = r % 3 := by omega
  rw [hr3] at h3
  rw [hr] at h9
  clear hr hr3
  generalize m ^ 3 = x at h h9 ⊢
  interval_cases r
  all_goals first
    | (norm_num at h3; done)
    | (norm_num at h9; omega)

theorem three_dvd_of_orderOf_three {p n : ℕ} {F : Type} [Field F] (hp : p.Prime) (hn : 1 ≤ n)
    (hcard : Nat.card F = p ^ n) {σ : F ≃+* F} (hσ : orderOf σ = 3) : 3 ∣ n := by
  obtain ⟨_, _, _, _, hAut, _⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality p n hp hn F
      hcard
  have : Finite (F ≃+* F) := Nat.finite_of_card_ne_zero (by rw [hAut]; omega)
  have h := orderOf_dvd_natCard σ
  rw [hσ, hAut] at h
  exact h

theorem nine_dvd_add_one_of_orderOf_three {ℓ f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) {σ : F ≃+* F} (hσ : orderOf σ = 3) (h3 : 3 ∣ ℓ ^ f + 1) :
    9 ∣ ℓ ^ f + 1 := by
  have hcard : Nat.card F = ℓ ^ (2 * f) := h.card
  have hn : 1 ≤ 2 * f := by
    have := h.one_le
    omega
  have h3n : 3 ∣ 2 * f := three_dvd_of_orderOf_three h.prime hn hcard hσ
  have h3f : 3 ∣ f := by omega
  obtain ⟨k, hk⟩ := h3f
  have hq : ℓ ^ f = (ℓ ^ k) ^ 3 := by
    rw [hk, pow_mul']
  rw [hq] at h3 ⊢
  have hr : ((ℓ ^ k) ^ 3 + 1) % 9 = 0 := cube_add_one_mod_nine_of_mod_three (ℓ ^ k) (by omega)
  omega

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

end
