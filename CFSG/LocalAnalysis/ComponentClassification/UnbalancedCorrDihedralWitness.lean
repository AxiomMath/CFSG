module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

variable {G : Type*} [Group G]

theorem le_pPrimeCore_of_normal_of_odd {X : Type*} [Group X] {N : Subgroup X} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ pPrimeCore 2 X := by
  unfold pPrimeCore
  exact le_sSup ⟨hN, Nat.coprime_two_left.mpr hodd⟩

variable [Finite G]

theorem odd_card_map_pPrimeCore (K : Subgroup G) :
    Odd (Nat.card ((pPrimeCore 2 K).map K.subtype)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_map_of_injective K.subtype_injective]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

end CFSG.ComponentClassification.UnbalancedCorr
