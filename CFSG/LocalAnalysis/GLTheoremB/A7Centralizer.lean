module

public import CFSG.LocalAnalysis.GLTheoremB.S7Decide
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.LocalAnalysis.GLTheoremB

namespace S7

open Equiv Equiv.Perm

theorem isSimple_Alt7 : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem not_isPGroup_two_Alt7 : ¬ IsPGroup 2 ↥(alternatingGroup (Fin 7)) := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_card_eq
  have hcard : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [hcard] at hn
  have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 2520)
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem card_centralizer_dvd_72 {τ : S} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    Nat.card ↥(Subgroup.centralizer ({τ} : Set S)) ∣ 72 := by
  have hdvd : orderOf τ ∣ 3 := orderOf_dvd_of_pow_eq_one hτ
  have hall : ∀ c ∈ τ.cycleType, c = 3 := by
    intro c hc
    have h1 : c ∣ orderOf τ := by
      rw [← Equiv.Perm.lcm_cycleType]
      exact Multiset.dvd_lcm hc
    have h2 : c ∣ 3 := h1.trans hdvd
    have h3 : 2 ≤ c := Equiv.Perm.two_le_of_mem_cycleType hc
    have : c ≤ 3 := Nat.le_of_dvd (by norm_num) h2
    interval_cases c
    · exact absurd h2 (by norm_num)
    · rfl
  have hne : τ.cycleType ≠ 0 := fun h => hτ1 (Equiv.Perm.cycleType_eq_zero.1 h)
  have hsum : τ.cycleType.sum ≤ 7 := by
    rw [Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hrep : τ.cycleType = Multiset.replicate (Multiset.card τ.cycleType) 3 :=
    Multiset.eq_replicate.2 ⟨rfl, hall⟩
  set k := Multiset.card τ.cycleType with hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact absurd (Multiset.card_eq_zero.1 h) hne
    · exact h
  have hk2 : k ≤ 2 := by
    rw [hrep, Multiset.sum_replicate] at hsum
    simp at hsum
    omega
  have hcard := Equiv.Perm.nat_card_centralizer τ
  rw [hrep] at hcard
  interval_cases k
  · simp at hcard
    rw [hcard]
    norm_num [Nat.factorial]
  · simp at hcard
    rw [hcard]
    norm_num

theorem eq_bot_of_perfect_le_centralizer {τ : S} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {P : Subgroup S}
    (hP : P ≤ Subgroup.centralizer ({τ} : Set S)) (hperf : ⁅P, P⁆ = P) : P = ⊥ := by
  by_contra hne
  have hdvd : Nat.card ↥P ∣ 72 :=
    (Subgroup.card_dvd_of_le hP).trans (card_centralizer_dvd_72 hτ hτ1)
  have hsolv : Group.IsSolvable ↥P := by
    refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
    have hsub : (Nat.card ↥P).primeFactors ⊆ ({2, 3} : Finset ℕ) := by
      intro q hq
      obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.1 hq
      have hq72 : q ∣ 2 ^ 3 * 3 ^ 2 := by
        have := hqd.trans hdvd
        norm_num
        exact this
      rcases (Nat.Prime.dvd_mul hqp).1 hq72 with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).1 (hqp.dvd_of_dvd_pow h)
        simp [this]
      · have := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_three).1 (hqp.dvd_of_dvd_pow h)
        simp [this]
    exact (Finset.card_le_card hsub).trans (by simp)
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hperf
  have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hne
  exact Group.IsPerfect.not_isSolvable ↥P hsolv

end S7

end CFSG.LocalAnalysis.GLTheoremB
