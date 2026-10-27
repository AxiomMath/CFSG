module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.K432

open Equiv Equiv.Perm

variable {n : ℕ}

theorem cycleType_eq_three_of_pow_three {g : Perm (Fin n)} (hg : g ^ 3 = 1) :
    ∀ c ∈ g.cycleType, c = 3 := by
  intro c hc
  have h1 : c ∣ orderOf g := dvd_of_mem_cycleType hc
  have h2 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg
  have h3 : 2 ≤ c := two_le_of_mem_cycleType hc
  have h4 : c ∣ 3 := h1.trans h2
  rcases (Nat.dvd_prime Nat.prime_three).mp h4 with h | h
  · omega
  · exact h

theorem exists_odd_mem_centralizer_of_pow_three (hn : 5 ≤ n) {g : Perm (Fin n)}
    (hg : g ^ 3 = 1) :
    ∃ c : Perm (Fin n), c * g = g * c ∧ c ∉ alternatingGroup (Fin n) := by
  by_contra hcon
  push Not at hcon
  have hle : Subgroup.centralizer {g} ≤ alternatingGroup (Fin n) := by
    intro c hc
    exact hcon c (Subgroup.mem_centralizer_singleton_iff.mp hc)
  obtain ⟨-, hcard, hcount⟩ := centralizer_le_alternating_iff.mp hle
  have h3 := cycleType_eq_three_of_pow_three hg
  have hrep : g.cycleType = Multiset.replicate (Multiset.card g.cycleType) 3 :=
    Multiset.eq_replicate.mpr ⟨rfl, h3⟩
  have hsum : g.cycleType.sum = 3 * Multiset.card g.cycleType := by
    rw [hrep, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul, mul_comm]
  have hk : Multiset.card g.cycleType ≤ 1 := by
    have := hcount 3
    rw [hrep, Multiset.count_replicate_self] at this
    exact this
  rw [Fintype.card_fin, hsum] at hcard
  omega

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.K432
