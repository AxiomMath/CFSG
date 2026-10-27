module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory

theorem not_dvd_card_of_isPGroup {G : Type*} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (hq : q.Prime) (hqp : q ≠ p) : ¬ q ∣ Nat.card G := by
  obtain ⟨n, hn⟩ := hG.exists_card_eq
  rw [hn]
  exact fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp (hq.dvd_of_dvd_pow h))

end CFSG.GroupTheory
