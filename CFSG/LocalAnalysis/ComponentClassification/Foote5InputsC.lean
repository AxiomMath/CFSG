module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Setting
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Inputs

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.FooteLit

@[expose] def Foote5DiagonalNotInQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L₀ L Q S T : Subgroup G) (z t : G),
    Sec5 G L₀ L Q S T z t → Foote5AutStructure →
    (∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) → 4 < Nat.card Q →
    (∀ y ∈ T, y * t = t * y → y ∈ S) → Nat.card T = 2 * Nat.card S →
    ∀ s ∈ T, s ∉ S → ∀ r ∈ conjugate (S ⊓ L) s, r * r = 1 → r * t ∉ Q

end CFSG.ComponentClassification.Foote5
