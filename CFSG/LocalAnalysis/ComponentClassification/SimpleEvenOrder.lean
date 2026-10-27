module

public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.LocalAnalysis.ComponentInitial.SmallGroupFacts

public section

namespace CFSG.ComponentClassification.SimpleEvenOrder

theorem nonabelian_simple_even {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Even (Nat.card G) ∧ ∃ x : G, orderOf x = 2 := by
  have heven : Even (Nat.card G) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (CFSG.LocalAnalysis.ComponentInitial.solvable_simple_abelian
      (CFSG.Milestones.odd_order_solvable hodd) a b)
  refine ⟨heven, ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)

end CFSG.ComponentClassification.SimpleEvenOrder
