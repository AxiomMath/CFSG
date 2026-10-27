module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.CharAndCard

public section

namespace CFSG.LieType.Ree

theorem three_pow_odd (a : ℕ) : Odd (3 ^ a) := Odd.pow (by decide)

theorem gcd_two_mul_three_pow_sub_one (a : ℕ) :
    Nat.gcd (2 * 3 ^ a - 1) (3 ^ (2 * a + 1) - 1) = 1 := by
  have hθ : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by norm_num)
  have hq1 : 1 ≤ 3 ^ (2 * a + 1) := Nat.one_le_pow _ _ (by norm_num)
  have h : IsCoprime ((2 * 3 ^ a - 1 : ℕ) : ℤ) ((3 ^ (2 * a + 1) - 1 : ℕ) : ℤ) := by
    refine ⟨3 * (2 * (3 ^ a : ℤ) + 1), -4, ?_⟩
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * 3 ^ a), Nat.cast_sub hq1]
    ring
  exact Nat.isCoprime_iff_coprime.mp h

theorem gcd_three_pow_sub_one (a : ℕ) :
    Nat.gcd (3 ^ a - 1) (3 ^ (2 * a + 1) - 1) = 2 := by
  have hθ : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by norm_num)
  have hq : 3 ^ (2 * a + 1) - 1 = 2 + (3 * 3 ^ a + 3) * (3 ^ a - 1) := by
    have h3 : 3 ^ (2 * a + 1) = 3 * (3 ^ a) ^ 2 := by ring
    rw [h3]
    zify [hθ, (by nlinarith : 1 ≤ 3 * (3 ^ a) ^ 2)]
    ring
  rw [hq, Nat.gcd_add_mul_right_right]
  obtain ⟨m, hm⟩ := three_pow_odd a
  exact Nat.gcd_eq_right ⟨m, by omega⟩

theorem small_Ree_field_power_identities (a : ℕ) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    CharP K 3 ∧
    ∃ ρ σ : K ≃+* K, (∀ x, ρ x = x ^ 3 ^ a) ∧ (∀ x, σ x = x ^ (3 * 3 ^ a)) ∧
      ρ.trans σ = RingEquiv.refl K ∧ σ.trans ρ = RingEquiv.refl K ∧
      (∀ x, σ (σ x) = x ^ 3) ∧ (1 ≤ a → σ ≠ RingEquiv.refl K) ∧
      Nat.gcd (2 * 3 ^ a - 1) (3 ^ (2 * a + 1) - 1) = 1 ∧
      Nat.gcd (3 ^ a - 1) (3 ^ (2 * a + 1) - 1) = 2 ∧
      Function.Bijective (fun s : Kˣ => s ^ (2 * 3 ^ a - 1)) ∧
      Nat.card (Set.range fun s : Kˣ => s ^ (1 - (3 ^ a : ℤ))) = (3 ^ (2 * a + 1) - 1) / 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Fintype.card K = 3 ^ (2 * a + 1) := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 3 := charP_of_card_eq_prime_pow hcard
  have hpowq : ∀ x : K, x ^ 3 ^ (2 * a + 1) = x := fun x => by
    rw [← hcard, FiniteField.pow_card]
  set ρ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 3 a)
    (iterateFrobenius K 3 a).injective.bijective_of_finite with hρ
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 3 (a + 1))
    (iterateFrobenius K 3 (a + 1)).injective.bijective_of_finite with hσ
  have hρx : ∀ x, ρ x = x ^ 3 ^ a := fun x => iterateFrobenius_def (p := 3) a x
  have hσx : ∀ x, σ x = x ^ (3 * 3 ^ a) := fun x => by
    rw [← pow_succ']
    exact iterateFrobenius_def (p := 3) (a + 1) x
  have hexp : 3 ^ a * (3 * 3 ^ a) = 3 ^ (2 * a + 1) := by ring
  refine ⟨inferInstance, ρ, σ, hρx, hσx, ?_, ?_, fun x => ?_, fun ha hσ1 => ?_,
    gcd_two_mul_three_pow_sub_one a, gcd_three_pow_sub_one a, ?_, ?_⟩
  · refine RingEquiv.ext fun x => ?_
    rw [RingEquiv.trans_apply, hσx, hρx, ← pow_mul, hexp, hpowq, RingEquiv.refl_apply]
  · refine RingEquiv.ext fun x => ?_
    rw [RingEquiv.trans_apply, hρx, hσx, ← pow_mul, mul_comm, hexp, hpowq,
      RingEquiv.refl_apply]
  · rw [hσx, hσx, ← pow_mul, show 3 * 3 ^ a * (3 * 3 ^ a) = 3 ^ (2 * a + 1) * 3 by ring,
      pow_mul, hpowq]
  ·
    have hlt : 1 < 3 * 3 ^ a := by have := Nat.one_le_pow a 3 (by norm_num); omega
    have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (Polynomial.X ^ (3 * 3 ^ a) - Polynomial.X : Polynomial K) (f := id) Function.injective_id
      (fun x => by
        have h := congrArg (fun e : K ≃+* K => e x) hσ1
        simp only [hσx, RingEquiv.refl_apply] at h
        simp [h])
      (by
        rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hlt, hcard]
        calc 3 * 3 ^ a < 3 * 3 ^ a * 3 ^ a := by
              have : 3 ≤ 3 ^ a := by
                calc 3 = 3 ^ 1 := by norm_num
                  _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha
              nlinarith
          _ = 3 ^ (2 * a + 1) := by ring)
    have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K hlt
    rw [hP, Polynomial.natDegree_zero] at hdeg
    omega
  · have hcop : (Nat.card Kˣ).Coprime (2 * 3 ^ a - 1) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units, hcard, Nat.Coprime, Nat.gcd_comm]
      exact gcd_two_mul_three_pow_sub_one a
    have h := (powCoprime hcop).bijective
    exact h
  · have hθ : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by norm_num)
    have hrange : (Set.range fun s : Kˣ => s ^ (1 - (3 ^ a : ℤ))) =
        ((powMonoidHom (3 ^ a - 1) : Kˣ →* Kˣ).range : Set Kˣ) := by
      ext y
      simp only [Set.mem_range, MonoidHom.coe_range, powMonoidHom_apply]
      have hz : ∀ s : Kˣ, s ^ (1 - (3 ^ a : ℤ)) = s⁻¹ ^ (3 ^ a - 1) := fun s => by
        rw [inv_pow, ← zpow_natCast, ← zpow_neg]
        push_cast [Nat.cast_sub hθ]
        ring_nf
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨s⁻¹, (hz s).symm⟩
      · rintro ⟨s, rfl⟩
        exact ⟨s⁻¹, by rw [hz, inv_inv]⟩
    rw [hrange, Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    change Nat.card (powMonoidHom (3 ^ a - 1) : Kˣ →* Kˣ).range = _
    rw [IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, Fintype.card_units, hcard,
      Nat.gcd_comm, gcd_three_pow_sub_one]

end CFSG.LieType.Ree
