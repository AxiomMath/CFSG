module

public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteCharacters
public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteOrderAverages

public section

open scoped BigOperators Classical

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers

theorem fourier_trace_natural {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (n : ℕ) (hn : 0 < n) (A : Module.End ℂ V) (hA : A ^ n = 1) (eigenvalue : ℂˣ)
    (heigenvalue : eigenvalue ^ n = 1) :
    ∃ m : ℕ, (n : ℂ)⁻¹ * ∑ j ∈ Finset.range n,
      ((eigenvalue⁻¹ : ℂˣ) : ℂ) ^ j * LinearMap.trace ℂ V (A ^ j) = m := by
  let nUnit : ℂˣ := Units.mk0 (n : ℂ) (Nat.cast_ne_zero.mpr hn.ne')
  have hnUnit : (nUnit : ℂ) = n := rfl
  set P := finiteOrderEigenprojection n nUnit eigenvalue A with hP
  have hidem : IsIdempotentElem P :=
    finiteOrderEigenprojection_idempotent n nUnit eigenvalue hnUnit heigenvalue A hA
  have htrace : LinearMap.trace ℂ V P = (Module.finrank ℂ (LinearMap.range P) : ℂ) :=
    (LinearMap.IsIdempotentElem.isProj_range P hidem).trace
  refine ⟨Module.finrank ℂ (LinearMap.range P), ?_⟩
  rw [← htrace, hP]
  simp only [finiteOrderEigenprojection, cyclicOperatorAverage, map_smul, map_sum, smul_pow,
    smul_eq_mul]
  rw [show ((nUnit⁻¹ : ℂˣ) : ℂ) = (n : ℂ)⁻¹ by rw [Units.val_inv_eq_inv_val, hnUnit]]

theorem character_fourier_natural {G : Type*} [Group G] (data : FiniteComplexRepresentation G)
    (g : G) (n : ℕ) (hn : 0 < n) (hg : data.representation g ^ n = 1) (eigenvalue : ℂˣ)
    (heigenvalue : eigenvalue ^ n = 1) :
    ∃ m : ℕ, (n : ℂ)⁻¹ * ∑ j ∈ Finset.range n,
      ((eigenvalue⁻¹ : ℂˣ) : ℂ) ^ j * data.character (g ^ j) = m := by
  obtain ⟨m, hm⟩ := fourier_trace_natural n hn (data.representation g) hg eigenvalue heigenvalue
  refine ⟨m, ?_⟩
  rw [← hm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FiniteComplexRepresentation.character, Representation.character, map_pow]

end CFSG.LyonsUnitaryFour
