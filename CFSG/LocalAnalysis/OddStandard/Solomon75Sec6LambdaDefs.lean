module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Defs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def Sec6Lambda1At (X : Type) [Group X] (n : ℕ) (t : X) : Prop :=
  ∀ a ∈ Sec6M X n (cen t), ∀ b ∈ Sec6M X n (cen t), orderOf a = 2 → orderOf b = 2 →
    a * b = b * a → oddCoreOf (cen a) ⊓ cen b ≤ oddCoreOf (cen b)

end CFSG.OddStandard.Solomon75
