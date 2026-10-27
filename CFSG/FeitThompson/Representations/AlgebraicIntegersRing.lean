module

public import CFSG.FeitThompson.Representations.StableModuleAlgebraicIntegrality
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Polynomial ComplexConjugate

theorem mem_integralClosure_int_complex_iff (z : ℂ) :
    z ∈ integralClosure ℤ ℂ ↔ ∃ p : ℤ[X], p.Monic ∧ 0 < p.natDegree ∧ aeval z p = 0 := by
  rw [mem_integralClosure_iff, isIntegral_int_iff_exists_monic_natDegree_pos]

theorem coe_toSubring_integralClosure_int_complex :
    ((integralClosure ℤ ℂ).toSubring : Set ℂ)
      = {z : ℂ | ∃ p : ℤ[X], p.Monic ∧ 0 < p.natDegree ∧ aeval z p = 0} :=
  Set.ext fun z => mem_integralClosure_int_complex_iff z

theorem intCast_mem_integralClosure_int_complex (n : ℤ) : (n : ℂ) ∈ integralClosure ℤ ℂ :=
  isIntegral_intCast n

theorem range_intCast_subset_integralClosure_int_complex :
    Set.range (Int.cast : ℤ → ℂ) ⊆ ((integralClosure ℤ ℂ).toSubring : Set ℂ) := by
  rintro _ ⟨n, rfl⟩
  exact intCast_mem_integralClosure_int_complex n

theorem aeval_conj_int (p : ℤ[X]) (z : ℂ) : aeval (conj z) p = conj (aeval z p) := by
  simpa using aeval_algHom_apply (R := ℤ) (starRingEnd ℂ).toIntAlgHom z p

theorem isIntegral_int_conj {z : ℂ} (hz : IsIntegral ℤ z) : IsIntegral ℤ (conj z) :=
  map_isIntegral_int (starRingEnd ℂ) hz

@[simp]
theorem isIntegral_int_conj_iff {z : ℂ} : IsIntegral ℤ (conj z) ↔ IsIntegral ℤ z :=
  ⟨fun h => by simpa using isIntegral_int_conj h, isIntegral_int_conj⟩

theorem conj_mem_integralClosure_int_complex {z : ℂ} (hz : z ∈ integralClosure ℤ ℂ) :
    conj z ∈ integralClosure ℤ ℂ :=
  isIntegral_int_conj hz

theorem map_starRingEnd_integralClosure_int_complex :
    (integralClosure ℤ ℂ).toSubring.map (starRingEnd ℂ) = (integralClosure ℤ ℂ).toSubring := by
  ext x
  simp only [Subring.mem_map, Subalgebra.mem_toSubring]
  refine ⟨?_, fun hx => ⟨conj x, conj_mem_integralClosure_int_complex hx, by simp⟩⟩
  rintro ⟨y, hy, rfl⟩
  exact conj_mem_integralClosure_int_complex hy

theorem exists_monic_natDegree_pos_sum {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (h : ∀ i ∈ s, ∃ p : ℤ[X], p.Monic ∧ 0 < p.natDegree ∧ aeval (z i) p = 0) :
    ∃ p : ℤ[X], p.Monic ∧ 0 < p.natDegree ∧ aeval (∑ i ∈ s, z i) p = 0 := by
  rw [← isIntegral_int_iff_exists_monic_natDegree_pos]
  exact IsIntegral.sum _ fun i hi =>
    (isIntegral_int_iff_exists_monic_natDegree_pos (z i)).2 (h i hi)

theorem exists_monic_natDegree_pos_prod {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (h : ∀ i ∈ s, ∃ p : ℤ[X], p.Monic ∧ 0 < p.natDegree ∧ aeval (z i) p = 0) :
    ∃ p : ℤ[X], p.Monic ∧ 0 < p.natDegree ∧ aeval (∏ i ∈ s, z i) p = 0 := by
  rw [← isIntegral_int_iff_exists_monic_natDegree_pos]
  exact IsIntegral.prod _ fun i hi =>
    (isIntegral_int_iff_exists_monic_natDegree_pos (z i)).2 (h i hi)

end CFSG.FeitThompson
