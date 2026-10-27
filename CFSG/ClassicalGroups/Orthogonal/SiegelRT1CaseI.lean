module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1CaseIDim4

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}

theorem not_caseI (hs : Setting hBN Qf ρ) : ¬ CaseI hBN ρ := by
  intro hI
  rcases (show finrank K N = 4 ∨ 5 ≤ finrank K N by have := hs.dimN; omega) with h | h
  · exact false_of_caseI_of_finrank_four hs hI h
  · exact false_of_caseI_of_five_le hs hI h

theorem caseII_of_setting (hs : Setting hBN Qf ρ) :
    ∀ a c : N, LinearIndependent K ![a, c] → BN a c = 0 →
      axis hBN ρ a 1 ⊓ axis hBN ρ c 1 = ⊥ :=
  (caseI_or_caseII hs).resolve_left (not_caseI hs)

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
