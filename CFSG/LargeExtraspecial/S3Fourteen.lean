module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

namespace CFSG.LargeExtraspecial

open Subgroup
open scoped commutatorElement

variable {P : Type*} [Group P]

theorem isExtraspecialPGroup_of_card_center [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    (hZ : Nat.card (center P) = p) (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ center P)
    (hpow : ∀ x : P, x ^ p ∈ center P) (hnc : ∃ x y : P, x * y ≠ y * x) :
    IsExtraspecialPGroup p P := by
  have hle : commutator P ≤ center P := by
    rw [_root_.commutator_def, commutator_le]
    intro x _ y _
    exact hcomm x y
  have hne : commutator P ≠ ⊥ := by
    obtain ⟨x, y, hxy⟩ := hnc
    intro h
    apply hxy
    have : ⁅x, y⁆ ∈ commutator P := by
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (mem_top x) (mem_top y)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have heq : commutator P = center P := by
    have hdvd : Nat.card (commutator P) ∣ p := hZ ▸ card_dvd_of_le hle
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h1 | h1
    · exact absurd (eq_bot_of_card_eq _ h1) hne
    · exact eq_of_le_of_card_ge hle (by rw [hZ, h1])
  refine ⟨hP, heq,
    le_antisymm (CFSG.SectionRank.Ccomm.frattini_le_of_commutator_pow_mem (center P) hcomm hpow)
      ?_, hZ⟩
  rw [← heq, _root_.commutator_def, commutator_le]
  intro x _ y _
  exact CFSG.SectionRank.Ccomm.commutator_mem_frattini hP x y

variable [Finite P] {p : ℕ} [hp : Fact p.Prime]

end CFSG.LargeExtraspecial
