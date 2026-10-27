module

public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

structure Tables112More : Prop where
  T10_16 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K → (IsHatSix K ∨ IsHatSeven K ∨ IsHatMTwentyTwo K) →
      2 ≤ GLATwoLocalRank 3 K
  T10_18_3 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K → (IsSLThreeExc K ∨ IsSUThreeExc K) → GLATwoLocalRank 3 K = 1 →
      IsSUThreeTwoPow K
  T10_10S : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K →
    (IsHatSix K ∨ IsHatSeven K ∨ IsHatMTwentyTwo K ∨ IsSLThreeExc K ∨ IsSUThreeExc K) →
      ∀ R : Sylow 3 K, Nat.card ↥(R : Subgroup K) = 27 ∧
        (∃ r ∈ (R : Subgroup K), ∃ s ∈ (R : Subgroup K), r * s ≠ s * r) ∧
        ∀ r ∈ (R : Subgroup K), r ^ 3 = 1

end CFSG.HardMathSupport.Solomon.Coordinator
