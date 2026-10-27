module

public import Mathlib.GroupTheory.Perm.Centralizer

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

private lemma cycleType_eq_singleton_of_prime_order (g : Equiv.Perm (Fin 8)) {p : ℕ}
    (hp : p.Prime) (hp4 : 4 < p) (hg : orderOf g = p) : g.cycleType = {p} := by
  have hprime : (orderOf g).Prime := by rwa [hg]
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hprime
  rw [hg] at hn
  have hsum : (Multiset.replicate (n + 1) p).sum ≤ 8 := by
    have h := Equiv.Perm.sum_cycleType_le g
    rw [hn] at h
    simpa using h
  simp only [Multiset.sum_replicate, smul_eq_mul] at hsum
  have hp5 : 5 ≤ p := by omega
  have h5 : (n + 1) * 5 ≤ 8 := (Nat.mul_le_mul_left (n + 1) hp5).trans hsum
  have hn0 : n = 0 := by omega
  rw [hn0] at hn
  simpa only [Nat.zero_add, Multiset.replicate_one] using hn

theorem gamma_perm_card_centralizer_seven (g : Equiv.Perm (Fin 8)) (hg : orderOf g = 7) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 8)))) = 7 := by
  have hct : g.cycleType = {7} :=
    cycleType_eq_singleton_of_prime_order g (by decide) (by decide) hg
  rw [Equiv.Perm.nat_card_centralizer g, hct]
  decide

theorem gamma_perm_card_centralizer_five (g : Equiv.Perm (Fin 8)) (hg : orderOf g = 5) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 8)))) = 30 := by
  have hct : g.cycleType = {5} :=
    cycleType_eq_singleton_of_prime_order g (by decide) (by decide) hg
  rw [Equiv.Perm.nat_card_centralizer g, hct]
  decide

end CFSG.EvenSporadicStandard.HNRecog.Section3
