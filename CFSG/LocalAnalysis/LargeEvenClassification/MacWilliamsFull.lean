module

public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsAssembly
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourExtension

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem rank_two_large_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    {upper lower : ℕ} (hlower : 0 < lower) (hordered : lower ≤ upper)
    (hlarge : 4 ≤ upper + lower)
    (coordinates : A ≃* Multiplicative (ZMod (2 ^ upper)) ×
      Multiplicative (ZMod (2 ^ lower))) (U : Subgroup S) :
    ∃ X : Finset U, Subgroup.closure (X : Set U) = ⊤ ∧ X.card ≤ 4 := by
  exact rank_two_large_four_generators_of_c8_four hpgroup hnoEight
    (fun A _ hcommutative hselfCentralizing coordinates =>
      c8_four_coordinate_four_generators hpgroup A hcommutative hselfCentralizing
        hnoEight coordinates)
    A hcommutative hselfCentralizing hlower hordered hlarge coordinates U

theorem macwilliams_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8) :
    ∀ U : Subgroup S, ∃ X : Finset S, X.card ≤ 4 ∧ Subgroup.closure (X : Set S) = U := by
  exact macwilliams_four_generators_of_c8_four hpgroup hnoEight
    (fun A _ hcommutative hselfCentralizing coordinates =>
      c8_four_coordinate_four_generators hpgroup A hcommutative hselfCentralizing
        hnoEight coordinates)

end CFSG.LargeEvenClassification.Helpers
