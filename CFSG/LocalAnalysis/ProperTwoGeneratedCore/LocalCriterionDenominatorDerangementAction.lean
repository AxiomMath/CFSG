module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorFreeAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

variable {G X : Type*} [Group G] [MulAction G X]

theorem odd_actor_fixed_of_square_fixed (g : G) (hodd : Odd (orderOf g))
    (a : X) (hfix : g ^ 2 • a = a) : g • a = a := by
  have hfixn : ∀ n : ℕ, (g ^ 2) ^ n • a = a := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hfix, ih]
  obtain ⟨n, hn⟩ := exists_pow_eq_pow_two_mul (pow_orderOf_eq_one g) hodd 1
  simpa only [← pow_mul, ← hn, pow_one] using hfixn n

theorem derangement_order_odd_of_involution_unique_fixed [Finite G]
    (hunique : ∀ t : G, orderOf t = 2 → ∃! a : X, t • a = a)
    (g : G) (hg : ∀ a : X, g • a ≠ a) : Odd (orderOf g) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.zpowers g) 2 (by simpa only [Nat.card_zpowers] using
      (even_iff_two_dvd.mp heven))
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  obtain ⟨a, ha, huniq⟩ := hunique t htG
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp t.property
  have hgt : Commute g (t : G) := by rw [← hn]; exact Commute.self_zpow g n
  have hga : (t : G) • (g • a) = g • a := by
    rw [← mul_smul, ← hgt.eq, mul_smul, ha]
  exact hg a (huniq (g • a) hga)

theorem odd_derangement_full_centralizer_free
    (hthree : ∀ x : G, x ≠ 1 → ∀ a b c : X,
      a ≠ b → a ≠ c → b ≠ c →
        ¬ (x • a = a ∧ x • b = b ∧ x • c = c))
    (g : G) (hodd : Odd (orderOf g)) (hg : ∀ a : X, g • a ≠ a) :
    ∀ c : Subgroup.centralizer ({g} : Set G), ∀ a : X,
      (c : G) • a = a → c = 1 := by
  intro c a hca
  by_contra hc
  have hcG : (c : G) ≠ 1 := fun h => hc (Subtype.ext h)
  have hcg : Commute (c : G) g := Subgroup.mem_centralizer_singleton_iff.mp c.property
  have hcb : (c : G) • (g • a) = g • a := by
    rw [← mul_smul, hcg.eq, mul_smul, hca]
  have hcc : (c : G) • (g • (g • a)) = g • (g • a) := by
    rw [← mul_smul, hcg.eq, mul_smul, hcb]
  have hga : g • (g • a) = a := by
    by_contra h
    exact hthree c hcG a (g • a) (g • (g • a))
      (hg a).symm (fun e => h e.symm) (hg (g • a)).symm ⟨hca, hcb, hcc⟩
  exact hg a (odd_actor_fixed_of_square_fixed g hodd a (by
    simpa only [pow_two, mul_smul] using hga))

theorem odd_derangement_full_centralizer_card_dvd [Finite G] [Finite X]
    (hthree : ∀ x : G, x ≠ 1 → ∀ a b c : X,
      a ≠ b → a ≠ c → b ≠ c →
        ¬ (x • a = a ∧ x • b = b ∧ x • c = c))
    (g : G) (hodd : Odd (orderOf g)) (hg : ∀ a : X, g • a ≠ a) :
    Nat.card (Subgroup.centralizer ({g} : Set G)) ∣ Nat.card X :=
  free_action_card_dvd (odd_derangement_full_centralizer_free hthree g hodd hg)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
