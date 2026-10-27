module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.NumberTheory.Niven
public import Mathlib.Basic.Complex.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.DedekindDomain.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Polynomial

theorem isIntegral_iff_exists_monic_natDegree_pos {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] [Nontrivial A] {x : A} :
    IsIntegral R x ↔ ∃ p : R[X], p.Monic ∧ 0 < p.natDegree ∧ aeval x p = 0 := by
  refine ⟨fun ⟨p, hp, hpx⟩ => ⟨p, hp, ?_, hpx⟩, fun ⟨p, hp, _, hpx⟩ => ⟨p, hp, hpx⟩⟩
  rcases Nat.eq_zero_or_pos p.natDegree with h | h
  · rw [hp.natDegree_eq_zero.mp h] at hpx
    simp at hpx
  · exact h

theorem isIntegral_ratCast_iff_exists_int {α : Type*} [DivisionRing α] [CharZero α] (q : ℚ) :
    IsIntegral ℤ (q : α) ↔ ∃ n : ℤ, q = n := by
  rw [IsIntegral.ratCast_iff, IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)]
  simp [eq_comm]

theorem Complex.isIntegral_int_iff_exists_int_of_exists_rat {z : ℂ} (hz : ∃ q : ℚ, z = q) :
    IsIntegral ℤ z ↔ ∃ n : ℤ, z = n := by
  obtain ⟨q, rfl⟩ := hz
  rw [isIntegral_ratCast_iff_exists_int]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, by rw [hn]; push_cast; ring⟩, fun ⟨n, hn⟩ => ⟨n, by exact_mod_cast hn⟩⟩

theorem isIntegral_ratCast_iff_den_eq_one {α : Type*} [DivisionRing α] [CharZero α] (q : ℚ) :
    IsIntegral ℤ (q : α) ↔ q.den = 1 := by
  rw [isIntegral_ratCast_iff_exists_int, Rat.den_eq_one_iff]
  exact ⟨fun ⟨n, hn⟩ => by rw [hn]; simp, fun h => ⟨q.num, h.symm⟩⟩

end CFSG.FeitThompson
