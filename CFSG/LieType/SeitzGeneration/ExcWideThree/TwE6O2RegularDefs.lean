module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar


@[expose] def E6O2Regular : Prop :=
  ∀ w : WeylGroup Tag.E6, w ≠ 1 → ∀ c : ZMod 3, ∀ V : Finset (Fin Tag.E6.rank → ZMod 3),
    27 ≤ V.card →
    (∀ b ∈ V, w ∈ charStabilizer (triChar b) ∧
      triPairing b (e6Shift w) = c * triPairing b e6Omega3) →
    ∃ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α ∧ ∀ b ∈ V, triPairing b α = 0

end CFSG.LieType.SeitzGeneration.ExcWideThree
