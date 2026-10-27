module

public import CFSG.LocalAnalysis.SignalizerFunctor.TwoPrimeOrderSolvability

public section

namespace CFSG.LocalAnalysis.ComponentInitial

theorem isSolvable_of_card_primeFactors_le_two {G : Type*} [Group G] [Finite G]
    (h : (Nat.card G).primeFactors.card ≤ 2) : Group.IsSolvable G := by
  have hcard : Nat.card G ≠ 0 := Nat.card_pos.ne'
  obtain ⟨p, q, hp, hq, hpq⟩ : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
      ∀ r ∈ (Nat.card G).primeFactors, r = p ∨ r = q := by
    interval_cases hk : (Nat.card G).primeFactors.card
    · rw [Finset.card_eq_zero] at hk
      exact ⟨2, 2, Nat.prime_two, Nat.prime_two, fun r hr => by
        rw [hk] at hr
        simp at hr⟩
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hk
      have hpa : a.Prime := Nat.prime_of_mem_primeFactors (ha ▸ Finset.mem_singleton_self a)
      refine ⟨a, a, hpa, hpa, fun r hr => ?_⟩
      rw [ha, Finset.mem_singleton] at hr
      exact Or.inl hr
    · obtain ⟨a, b, -, hab⟩ := Finset.card_eq_two.mp hk
      refine ⟨a, b, Nat.prime_of_mem_primeFactors (hab ▸ Finset.mem_insert_self a {b}),
        Nat.prime_of_mem_primeFactors
          (hab ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)), fun r hr => ?_⟩
      rwa [hab, Finset.mem_insert, Finset.mem_singleton] at hr
  exact CFSG.SignalizerFunctor.Helpers.two_prime_order_solvable G p q hp hq
    fun r hr hdvd => hpq r (Nat.mem_primeFactors.mpr ⟨hr, hdvd, hcard⟩)

end CFSG.LocalAnalysis.ComponentInitial
