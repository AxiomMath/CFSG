module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.Basic.Complex.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Polynomial

theorem isIntegral_int_iff_exists_monic_natDegree_pos (z : ℂ) :
    IsIntegral ℤ z ↔ ∃ p : ℤ[X], p.Monic ∧ 0 < p.natDegree ∧ aeval z p = 0 := by
  constructor
  · rintro ⟨p, hmonic, hroot⟩
    rw [← aeval_def] at hroot
    refine ⟨p, hmonic, ?_, hroot⟩
    rcases Nat.eq_zero_or_pos p.natDegree with h | h
    · rw [hmonic.natDegree_eq_zero] at h
      rw [h, map_one] at hroot
      exact absurd hroot one_ne_zero
    · exact h
  · rintro ⟨p, hmonic, -, hroot⟩
    exact ⟨p, hmonic, by rwa [← aeval_def]⟩

theorem isIntegral_int_of_mul_mem_span {ι : Type*} [Finite ι] (v : ι → ℂ)
    (hv : ∃ i, v i ≠ 0) (z : ℂ)
    (hz : ∀ x ∈ Submodule.span ℤ (Set.range v), z * x ∈ Submodule.span ℤ (Set.range v)) :
    IsIntegral ℤ z := by
  obtain ⟨i, hi⟩ := hv
  refine isIntegral_of_smul_mem_submodule (R := ℤ) (A := ℂ) (M := ℂ)
    (Submodule.span ℤ (Set.range v)) ?_
    (Submodule.fg_span (Set.finite_range v)) z (by simpa [smul_eq_mul] using hz)
  intro h
  have hmem : v i ∈ Submodule.span ℤ (Set.range v) :=
    Submodule.subset_span (Set.mem_range_self i)
  rw [h, Submodule.mem_bot] at hmem
  exact hi hmem

theorem mem_span_iff_exists_intCast_sum {ι : Type*} [Fintype ι] (v : ι → ℂ) (x : ℂ) :
    x ∈ Submodule.span ℤ (Set.range v) ↔ ∃ a : ι → ℤ, ∑ i, (a i : ℂ) * v i = x := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  simp [zsmul_eq_mul]

theorem exists_monic_natDegree_pos_of_mul_mem {n : ℕ} (v : Fin n → ℂ) (hv : ∃ i, v i ≠ 0)
    (z : ℂ)
    (hz : ∀ a : Fin n → ℤ, ∃ b : Fin n → ℤ,
      z * ∑ i, (a i : ℂ) * v i = ∑ i, (b i : ℂ) * v i) :
    ∃ p : ℤ[X], p.Monic ∧ 0 < p.natDegree ∧ aeval z p = 0 := by
  rw [← isIntegral_int_iff_exists_monic_natDegree_pos]
  refine isIntegral_int_of_mul_mem_span v hv z ?_
  intro x hx
  obtain ⟨a, ha⟩ := (mem_span_iff_exists_intCast_sum v x).1 hx
  obtain ⟨b, hb⟩ := hz a
  exact (mem_span_iff_exists_intCast_sum v _).2 ⟨b, by rw [← hb, ha]⟩

end CFSG.FeitThompson
