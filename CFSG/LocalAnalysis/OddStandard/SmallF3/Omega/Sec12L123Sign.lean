module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec123_range_alt {C S : Subgroup G} (hSC : S ≤ C) (hodd : ¬ 2 ∣ S.relIndex C)
    (Θ : ↥C →* Equiv.Perm (Fin 5))
    (hS : ∀ s : ↥C, (s : G) ∈ S → Θ s ∈ alternatingGroup (Fin 5)) :
    ∀ m : ↥C, Θ m ∈ alternatingGroup (Fin 5) := by
  let ε : ↥C →* ℤˣ := Equiv.Perm.sign.comp Θ
  have hSker : S.subgroupOf C ≤ ε.ker := by
    intro s hs
    rw [MonoidHom.mem_ker]
    have hs' : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    have hsgn : Equiv.Perm.sign (Θ s) = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp (hS s hs')
    simpa [ε] using hsgn
  have hdvd_odd : ε.ker.index ∣ S.relIndex C := by
    have h := Subgroup.index_dvd_of_le hSker
    simpa only [Subgroup.relIndex] using h
  have hdvd_two : ε.ker.index ∣ 2 := by
    rw [Subgroup.index_ker]
    have h := Subgroup.card_subgroup_dvd_card ε.range
    rwa [show Nat.card ℤˣ = 2 by
      rw [Nat.card_eq_fintype_card, Fintype.card_units_int]] at h
  have hker1 : ε.ker.index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd_two with h | h
    · exact h
    · exact absurd (h ▸ hdvd_odd) hodd
  intro m
  rw [Equiv.Perm.mem_alternatingGroup]
  have hm : m ∈ ε.ker := by
    rw [Subgroup.index_eq_one.mp hker1]
    exact Subgroup.mem_top m
  rw [MonoidHom.mem_ker] at hm
  simpa [ε] using hm

end CFSG.OddStandard.SmallF3.Omega
