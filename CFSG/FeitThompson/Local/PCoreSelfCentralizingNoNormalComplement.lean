module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.FittingContainsCentralizerSolvable

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem pCore_eq_bot_of_pComplCore_eq_bot (h : pComplCore p X = ⊥) {q : ℕ} (hq : q.Prime)
    (hqp : q ≠ p) : pCore q X = ⊥ := by
  refine le_bot_iff.1 (h ▸ le_pComplCore (pCore_normal q X) ?_)
  intro hpmem
  obtain ⟨n, hn⟩ := exists_card_pCore_eq_pow hq X
  rw [hn] at hpmem
  have hpp := Nat.prime_of_mem_primeFactors hpmem
  exact hqp ((Nat.prime_dvd_prime_iff_eq hpp hq).1
    (hpp.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hpmem))).symm

theorem fittingRaw_eq_pCore_of_pComplCore_eq_bot (hp : p.Prime) (h : pComplCore p X = ⊥) :
    fittingRaw X = pCore p X := by
  rw [fittingRaw_eq_iSup_pCore]
  refine le_antisymm (iSup₂_le fun q hq => ?_)
    (le_iSup₂ (f := fun q (_ : q ∈ {q : ℕ | q.Prime}) => pCore q X) p hp)
  by_cases hqp : q = p
  · exact hqp ▸ le_rfl
  · rw [pCore_eq_bot_of_pComplCore_eq_bot h hq hqp]
    exact bot_le

theorem centralizer_pCore_le_pCore [Group.IsSolvable X] (hp : p.Prime) (h : pComplCore p X = ⊥) :
    centralizer (pCore p X : Set X) ≤ pCore p X := by
  rw [← fittingRaw_eq_pCore_of_pComplCore_eq_bot hp h]
  exact centralizer_fittingRaw_le_fittingRaw X

theorem pCore_ne_bot_of_pComplCore_eq_bot [Nontrivial X] [Group.IsSolvable X] (hp : p.Prime)
    (h : pComplCore p X = ⊥) : pCore p X ≠ ⊥ := by
  intro hbot
  have hbot' : centralizer ((⊥ : Subgroup X) : Set X) = ⊤ := by simp
  have hle := centralizer_pCore_le_pCore hp h
  rw [hbot, hbot'] at hle
  exact (bot_lt_top (α := Subgroup X)).ne (top_le_iff.1 hle)

theorem pCore_self_centralizing_of_pComplCore_eq_bot [Nontrivial X] [Group.IsSolvable X]
    (hp : p.Prime) (h : pComplCore p X = ⊥) :
    fittingRaw X = pCore p X ∧ pCore p X ≠ ⊥ ∧
      centralizer (pCore p X : Set X) ≤ pCore p X :=
  ⟨fittingRaw_eq_pCore_of_pComplCore_eq_bot hp h, pCore_ne_bot_of_pComplCore_eq_bot hp h,
    centralizer_pCore_le_pCore hp h⟩

end

end CFSG.FeitThompson
