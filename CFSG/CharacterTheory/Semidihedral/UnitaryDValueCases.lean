module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueThreeAdic
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueThreeSylow

public section

namespace CFSG.Semidihedral.UnitaryDValue

namespace DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem factorization_card_A_of_ne_three {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀2 : p₀ ≠ 2)
    (hp₀3 : p₀ ≠ 3) : (Nat.card D.A).factorization p₀ = (D.q + 1).factorization p₀ := by
  have : Fact p₀.Prime := ⟨hp₀⟩
  by_cases hdvd : p₀ ∣ D.q + 1
  · exact D.factorization_card_A_eq_of_dvd hp₀2 hp₀3 (D.prime_dvd_card_A hp₀ hp₀2 hp₀3 hdvd)
  · rw [Nat.factorization_eq_zero_of_not_dvd hdvd,
      Nat.factorization_eq_zero_of_not_dvd (fun h => hdvd (h.trans D.card_A_dvd))]

theorem gcd_q_add_one_three_of_dvd (h3 : 3 ∣ D.q + 1) : Nat.gcd (D.q + 1) 3 = 3 :=
  Nat.gcd_eq_right h3

theorem gcd_q_add_one_three_of_not_dvd (h3 : ¬ 3 ∣ D.q + 1) : Nat.gcd (D.q + 1) 3 = 1 :=
  (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))

theorem d_cases (hext : D.CharacterExtend) (htriv : D.CharacterTrivial) :
    D.m * Nat.card D.A * Nat.gcd (D.q + 1) 3 = D.q + 1 ∨
      ((Nat.card D.A).factorization 3 = 1 ∧ 3 ≤ (D.q + 1).factorization 3) := by
  have h3 : (D.m * Nat.card D.A * Nat.gcd (D.q + 1) 3).factorization 3 =
        (D.q + 1).factorization 3 ∨
      ((Nat.card D.A).factorization 3 = 1 ∧ 3 ≤ (D.q + 1).factorization 3) := by
    rw [fact_mul (Nat.mul_ne_zero D.m_pos.ne' D.card_A_pos.ne') (Nat.gcd_pos_of_pos_left _
      (by omega)).ne', fact_mul D.m_pos.ne' D.card_A_pos.ne', D.factorization_m (by norm_num),
      zero_add]
    by_cases hq3 : 3 ∣ D.q + 1
    · rw [D.gcd_q_add_one_three_of_dvd hq3, Nat.Prime.factorization_self Nat.prime_three]
      by_cases hA3 : 3 ∣ Nat.card D.A
      · rcases D.factorization_three_card_A hext htriv hA3 with h | h
        · exact Or.inl h.symm
        · exact Or.inr h
      · left
        rw [Nat.factorization_eq_zero_of_not_dvd hA3, zero_add]
        have h9 : ¬ 9 ∣ D.q + 1 := fun h9 => hA3 (D.three_dvd_card_A h9)
        have h1 : 1 ≤ (D.q + 1).factorization 3 :=
          (Nat.prime_three.dvd_iff_one_le_factorization (by omega)).mp hq3
        have h2 : (D.q + 1).factorization 3 < 2 := by
          by_contra hlt
          apply h9
          have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by omega)).mpr
            (not_lt.mp hlt)
          simpa using this
        omega
    · left
      rw [D.gcd_q_add_one_three_of_not_dvd hq3, Nat.factorization_one, Finsupp.zero_apply,
        add_zero, Nat.factorization_eq_zero_of_not_dvd hq3,
        Nat.factorization_eq_zero_of_not_dvd (fun h => hq3 (h.trans D.card_A_dvd))]
  rcases h3 with h3 | h3
  · left
    apply Nat.eq_of_factorization_eq
    · exact Nat.mul_ne_zero (Nat.mul_ne_zero D.m_pos.ne' D.card_A_pos.ne')
        (Nat.gcd_pos_of_pos_left _ (by omega)).ne'
    · omega
    intro p
    by_cases hp : p.Prime
    · by_cases hp3 : p = 3
      · subst hp3
        exact h3
      rw [fact_mul (Nat.mul_ne_zero D.m_pos.ne' D.card_A_pos.ne') (Nat.gcd_pos_of_pos_left _
        (by omega)).ne', fact_mul D.m_pos.ne' D.card_A_pos.ne']
      have hgcd : (Nat.gcd (D.q + 1) 3).factorization p = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hpd
        have h1 := (hpd.trans (Nat.gcd_dvd_right _ _))
        exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h1)
      rw [hgcd, add_zero]
      by_cases hp2 : p = 2
      · subst hp2
        have hA2 : (Nat.card D.A).factorization 2 = 0 := by
          apply Nat.factorization_eq_zero_of_not_dvd
          intro h
          have := Nat.odd_iff.mp D.A_odd
          omega
        rw [D.factorization_two_q_add_one, hA2, add_zero]
      · rw [D.factorization_m hp2, zero_add, D.factorization_card_A_of_ne_three hp hp2 hp3]
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]
  · exact Or.inr h3

end DValueData

end CFSG.Semidihedral.UnitaryDValue
