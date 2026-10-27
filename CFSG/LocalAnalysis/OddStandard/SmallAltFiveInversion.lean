module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveBasic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard

open Subgroup

open scoped commutatorElement

variable {G : Type*} [Group G] {P S : Subgroup G} {s x : G} {a : ℕ}

theorem eq_one_or_eq_of_mem_zpowers_of_mul_self_eq_one {t u : G} (htt : t * t = 1)
    (hu : u ∈ zpowers t) : u = 1 ∨ u = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hu
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, htt]
  rw [zpow_eq_zpow_emod k ht2]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [h0, zpow_zero]
  · right
    rw [h1, zpow_one]

end CFSG.OddStandard
