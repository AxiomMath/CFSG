module

public import CFSG.LocalAnalysis.Gross82.OrderThree
import CFSG.LocalAnalysis.Gross82.OrderThreeLinear
import CFSG.LocalAnalysis.Gross82.OrderThreeUnitary
import CFSG.LocalAnalysis.Gross82.POmegaPlusEight

public section

namespace CFSG.LocalAnalysis.Gross82

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)

section ResidualDispatch


theorem grossThreeInnerOrderThree_residual_of_E6
    (hE6 : ∀ (K : Type) [Group K] [Finite K] (n ℓ f : ℕ),
      StatedLieAdmissible .E6 n ℓ f → LieModel K .E6 n ℓ f →
        3 ∣ lieOrderDivisor .E6 n (ℓ ^ f) → IsSimpleGroup K → Subgroup.center K = ⊥ →
          3 ∣ Nat.card K → GrossThreeInnerOrderThree K)
    (h2E6 : ∀ (K : Type) [Group K] [Finite K] (n ℓ f : ℕ),
      StatedLieAdmissible .twistedE6 n ℓ f → LieModel K .twistedE6 n ℓ f →
        3 ∣ lieOrderDivisor .twistedE6 n (ℓ ^ f) → IsSimpleGroup K →
          Subgroup.center K = ⊥ → 3 ∣ Nat.card K → GrossThreeInnerOrderThree K) :
    ∀ (K : Type) [Group K] [Finite K] (t : StatedLieTag) (n ℓ f : ℕ),
      StatedLieAdmissible t n ℓ f → LieModel K t n ℓ f →
        (3 ∣ lieOrderDivisor t n (ℓ ^ f) ∨ (t = .POmegaPlus ∧ n = 4)) →
          IsSimpleGroup K → Subgroup.center K = ⊥ → 3 ∣ Nat.card K →
            GrossThreeInnerOrderThree K := by
  intro K _ _ t n ℓ f hadm hmodel hr hS hZ h3K
  rcases hr with h3 | ⟨rfl, rfl⟩
  · cases t
    case PSL =>
      exact grossThreeInnerOrderThree_PSL
        CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hadm hmodel h3
    case PSU =>
      exact grossThreeInnerOrderThree_PSU
        CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hadm hmodel h3
    case E6 => exact hE6 K n ℓ f hadm hmodel h3 hS hZ h3K
    case twistedE6 => exact h2E6 K n ℓ f hadm hmodel h3 hS hZ h3K
    all_goals norm_num [lieOrderDivisor, Nat.dvd_gcd_iff] at h3
  · exact grossThreeInnerOrderThree_POmegaPlus_four hadm hmodel

end ResidualDispatch

section Core



theorem r891GrossCoreOrderThree_of_E6
    (hE6 : ∀ (K : Type) [Group K] [Finite K] (n ℓ f : ℕ),
      StatedLieAdmissible .E6 n ℓ f → LieModel K .E6 n ℓ f →
        3 ∣ lieOrderDivisor .E6 n (ℓ ^ f) → IsSimpleGroup K → Subgroup.center K = ⊥ →
          3 ∣ Nat.card K → GrossThreeInnerOrderThree K)
    (h2E6 : ∀ (K : Type) [Group K] [Finite K] (n ℓ f : ℕ),
      StatedLieAdmissible .twistedE6 n ℓ f → LieModel K .twistedE6 n ℓ f →
        3 ∣ lieOrderDivisor .twistedE6 n (ℓ ^ f) → IsSimpleGroup K →
          Subgroup.center K = ⊥ → 3 ∣ Nat.card K → GrossThreeInnerOrderThree K) :
    R891GrossCoreOrderThree :=
  r891GrossCoreOrderThree_of_residual (grossThreeInnerOrderThree_residual_of_E6 hE6 h2E6)

end Core

end CFSG.LocalAnalysis.Gross82
