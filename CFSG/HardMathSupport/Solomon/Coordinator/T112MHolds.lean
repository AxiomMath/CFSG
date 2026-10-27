module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112MM22
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MLinear

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

theorem tables112More_T10_16_holds : ∀ (K : Type) [Group K] [Finite K],
    CFSG.Open.IsQuasisimple K → CFSG.Open.IsKGroup K →
    (IsHatSix K ∨ IsHatSeven K ∨ IsHatMTwentyTwo K) → 2 ≤ GLATwoLocalRank 3 K := by
  intro K _ _ _ _ h
  rcases h with h | h | h
  · exact t112m_twoLocal_hatSix h
  · exact t112m_twoLocal_hatSeven h
  · exact t112m_twoLocal_hatM22 h

theorem tables112More_T10_18_3_holds : ∀ (K : Type) [Group K] [Finite K],
    CFSG.Open.IsQuasisimple K → CFSG.Open.IsKGroup K → (IsSLThreeExc K ∨ IsSUThreeExc K) →
    GLATwoLocalRank 3 K = 1 → IsSUThreeTwoPow K :=
  fun _ _ _ hq _ h hw => t112m_T10_18_3 hq h hw

theorem tables112More_T10_10S_holds : ∀ (K : Type) [Group K] [Finite K],
    CFSG.Open.IsQuasisimple K → CFSG.Open.IsKGroup K →
    (IsHatSix K ∨ IsHatSeven K ∨ IsHatMTwentyTwo K ∨ IsSLThreeExc K ∨ IsSUThreeExc K) →
      ∀ R : Sylow 3 K, Nat.card ↥(R : Subgroup K) = 27 ∧
        (∃ r ∈ (R : Subgroup K), ∃ s ∈ (R : Subgroup K), r * s ≠ s * r) ∧
        ∀ r ∈ (R : Subgroup K), r ^ 3 = 1 := by
  intro K _ _ hq _ h R
  rcases h with h | h | h | h | h
  · exact t112m_sylow_hatSix h R
  · exact t112m_sylow_hatSeven h R
  · exact t112m_sylow_hatM22 h R
  · exact t112m_sylow_SL hq h R
  · exact t112m_sylow_SU hq h R

theorem tables112More_holds : Tables112More :=
  ⟨tables112More_T10_16_holds, tables112More_T10_18_3_holds, tables112More_T10_10S_holds⟩

end CFSG.HardMathSupport.Solomon.Coordinator
