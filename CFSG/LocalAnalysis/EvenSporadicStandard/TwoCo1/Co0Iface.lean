module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Assemble
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0Data
public import CFSG.Monster.Visible.SignFixed

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.ScalarKernel CFSG.Monster.Visible

structure Co0ClassData : Prop where
  involution_classes : ∀ y : latticeO, y * y = 1 → y ≠ 1 → y ≠ negOneO →
    ∃ c : latticeO, ∃ d ∈ ({oct₁, dod₂} : Set C),
      y = c * gO d * c⁻¹ ∨ y = negOneO * (c * gO d * c⁻¹)
  card_cent_oct : Nat.card (Subgroup.centralizer {gO oct₁}) = co0C2
  card_cent_dod : Nat.card (Subgroup.centralizer {gO dod₂}) = co0C3

end CFSG.EvenSporadicStandard.TwoCo1
