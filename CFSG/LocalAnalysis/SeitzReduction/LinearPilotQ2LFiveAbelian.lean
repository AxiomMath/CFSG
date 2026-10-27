module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

variable {X : Type*} [Group X]

theorem commute_right_of_commute_of_commute_mul {a t c : X} (ha : c * a = a * c)
    (hat : c * (a * t) = a * t * c) : c * t = t * c := by
  calc c * t = a⁻¹ * (c * a) * t := by rw [ha]; group
    _ = a⁻¹ * (c * (a * t)) := by group
    _ = a⁻¹ * (a * t * c) := by rw [hat]
    _ = t * c := by group

theorem inf_le_centralizer_of_index_eq_two_of_commute {A B : Subgroup X} (hA : A.index = 2)
    (hB : B.index = 2) (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hne : A ≠ B) (t : X) :
    A ⊓ B ≤ centralizer ({t} : Set X) := by
  have hAB : ¬ A ≤ B := by
    intro hle
    apply hne
    have hfin : B.FiniteIndex := ⟨by rw [hB]; exact two_ne_zero⟩
    have hrel : A.relIndex B * B.index = A.index := relIndex_mul_index hle
    rw [hA, hB] at hrel
    have h1 : A.relIndex B = 1 := by omega
    exact le_antisymm hle (relIndex_eq_one.1 h1)
  obtain ⟨a, haA, haB⟩ := IsConcreteLE.not_le_iff_exists.1 hAB
  intro c hc
  rw [mem_inf] at hc
  rw [mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  by_cases htA : y ∈ A
  · exact (hAc c hc.1 y htA).symm
  by_cases htB : y ∈ B
  · exact (hBc c hc.2 y htB).symm
  have hayB : a * y ∈ B := (mul_mem_iff_of_index_two hB).2 (iff_of_false haB htB)
  exact (commute_right_of_commute_of_commute_mul (hAc c hc.1 a haA) (hBc c hc.2 _ hayB)).symm

theorem eq_of_index_eq_two_of_commute [Finite X] {A B : Subgroup X} (hA : A.index = 2)
    (hB : B.index = 2) (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) {t : X}
    (hcard : Nat.card (centralizer ({t} : Set X)) < Nat.card (A ⊓ B : Subgroup X)) : A = B := by
  by_contra hne
  have hle := inf_le_centralizer_of_index_eq_two_of_commute hA hB hAc hBc hne t
  exact absurd (card_le_of_le hle) (not_le.2 hcard)

end CFSG.SeitzReduction.LinearPilot
