module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8

theorem card_eq_of_pow_two_mul_three {G : Type*} [Group G] [Finite G] (a b : ℕ)
    (hG : ∀ g : G, g ^ (2 ^ a * 3 ^ b) = 1) :
    Nat.card G = 2 ^ (Nat.card G).factorization 2 * 3 ^ (Nat.card G).factorization 3 := by
  have hn : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hsupp : (Nat.card G).factorization.support ⊆ {2, 3} := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpd, -⟩ := hp
    haveI := Fact.mk hpp
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpd
    have hdvd : p ∣ 2 ^ a * 3 ^ b := by
      rw [← hg]
      exact orderOf_dvd_of_pow_eq_one (hG g)
    rcases (Nat.Prime.dvd_mul hpp).1 hdvd with h | h
    · exact Finset.mem_insert.2 (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1
        (hpp.dvd_of_dvd_pow h)))
    · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2
        ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 (hpp.dvd_of_dvd_pow h))))
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => pow_zero _),
    Finset.prod_pair (by norm_num)]

theorem isSolvable_of_pow_two_mul_three {G : Type*} [Group G] [Finite G] (a b : ℕ)
    (hG : ∀ g : G, g ^ (2 ^ a * 3 ^ b) = 1) : Group.IsSolvable G := by
  haveI := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num)
    (by rw [Fintype.card_eq_nat_card]; exact card_eq_of_pow_two_mul_three a b hG)

theorem glaPLayer_eq_bot_of_isSolvable {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X : Subgroup G} [Group.IsSolvable X] : GLAPLayer p X = ⊥ := by
  refine eq_bot_iff.2 (sSup_le fun L hL g hg => ?_)
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val
    (CFSG.HardMathSupport.Solomon.Coordinator.hom_eq_one_of_solvable hp hL (MonoidHom.id X) g hg)

end CFSG.LocalAnalysis.GLTheoremA.H301
