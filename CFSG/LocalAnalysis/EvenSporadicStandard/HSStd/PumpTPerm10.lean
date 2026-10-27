module

public import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpT

open Equiv Subgroup

theorem cycleType_eq_of_orderOf_fifteen {g : Perm (Fin 10)} (hg : orderOf g = 15) :
    g.cycleType = {3, 5} := by
  have hlcm : g.cycleType.lcm = 15 := by rw [Perm.lcm_cycleType, hg]
  have hsum : g.cycleType.sum ≤ 10 := by simpa using Perm.sum_cycleType_le g
  have h2 : ∀ a ∈ g.cycleType, 2 ≤ a := fun a ha => Perm.two_le_of_mem_cycleType ha
  set m := g.cycleType with hm
  have h35 : ∀ a ∈ m, a = 3 ∨ a = 5 := by
    intro a ha
    have h2a := h2 a ha
    have hle : a ≤ 10 := (Multiset.le_sum_of_mem ha).trans hsum
    have hdvd : a ∣ 15 := hlcm ▸ Multiset.dvd_lcm ha
    interval_cases a <;> omega
  have h3m : 3 ∈ m := by
    by_contra h3
    have h5 : ∀ b ∈ m, b ∣ 5 := fun b hb => by
      rcases h35 b hb with rfl | rfl
      · exact absurd hb h3
      · exact dvd_rfl
    have := Multiset.lcm_dvd.2 h5
    rw [hlcm] at this
    omega
  have h5m : 5 ∈ m := by
    by_contra h5
    have h3 : ∀ b ∈ m, b ∣ 3 := fun b hb => by
      rcases h35 b hb with rfl | rfl
      · exact dvd_rfl
      · exact absurd hb h5
    have := Multiset.lcm_dvd.2 h3
    rw [hlcm] at this
    omega
  obtain ⟨m', hm'⟩ := Multiset.exists_cons_of_mem h3m
  have h5m' : 5 ∈ m' := by
    have h : 5 ∈ 3 ::ₘ m' := hm' ▸ h5m
    rcases Multiset.mem_cons.1 h with h | h
    · omega
    · exact h
  obtain ⟨m'', hm''⟩ := Multiset.exists_cons_of_mem h5m'
  have hsum' : m''.sum ≤ 2 := by
    have h : (3 ::ₘ 5 ::ₘ m'').sum ≤ 10 := by rw [← hm'', ← hm']; exact hsum
    simp only [Multiset.sum_cons] at h
    omega
  have hzero : m'' = 0 := by
    refine Multiset.eq_zero_of_forall_notMem fun a ha => ?_
    have hamem : a ∈ m := by rw [hm', hm'']; simp [ha]
    have h1 := Multiset.le_sum_of_mem ha
    have h3 := h35 a hamem
    omega
  rw [hm', hm'', hzero]
  rfl

theorem card_centralizer_eq_thirty {g : Perm (Fin 10)} (hg : orderOf g = 15) :
    Nat.card (centralizer ({g} : Set (Perm (Fin 10)))) = 30 := by
  rw [Perm.nat_card_centralizer, cycleType_eq_of_orderOf_fifteen hg]
  decide

end CFSG.EvenSporadicStandard.HSStd.PumpT
