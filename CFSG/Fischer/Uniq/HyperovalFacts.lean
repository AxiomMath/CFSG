module

public import CFSG.Fischer.Uniq.PolarIntrinsic

public section

namespace CFSG.Fischer

structure HyperovalFacts : Prop where
  linesByPerp : LinesByPerp
  isClosedHyperoval_of_mem : ∀ i, ∀ O ∈ hypOrbit i, IsClosedHyperoval O
  eq_of_inter_perp : ∀ O O', IsClosedHyperoval O → IsClosedHyperoval O' → ∀ p ∈ O, p ∈ O' →
    (∀ q, perp p q → (q ∈ O ↔ q ∈ O')) → O = O'
  not_linear : ∀ O, IsClosedHyperoval O → ∀ p ∈ O, ∀ q, ¬ perp p q →
    ¬ ∀ w, perp w p → w ≠ p → (w ∈ O ↔ perp w q)

end CFSG.Fischer
