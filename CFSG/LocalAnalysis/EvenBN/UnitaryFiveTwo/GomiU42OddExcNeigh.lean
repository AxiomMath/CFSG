module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcCount
public import CFSG.LieType.Chevalley.RationalToralSignDiagramDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def gomiNeighCount (τ : Tag) (b : Fin τ.rank → Bool) (a : List ℤ) : ℕ :=
  ((τ.artifactRoots).filter fun g => g != a &&
    decide (0 < ∑ i : Fin τ.rank, gomiRootVec g i) &&
    decide (Even (maskPairing b (gomiRootVec g : Fin τ.rank → ℤ))) &&
    decide (iform (τ := τ) (gomiRootVec a) (gomiRootVec g) ≠ 0)).length

@[expose] def gomiNeighOK (τ : Tag) (b : Fin τ.rank → Bool) : Bool :=
  (τ.artifactRoots).all fun a =>
    !(decide (0 < ∑ i : Fin τ.rank, gomiRootVec a i) &&
        decide (Even (maskPairing b (gomiRootVec a : Fin τ.rank → ℤ)))) ||
      (gomiNeighCount τ b a == 0 || decide (4 ≤ gomiNeighCount τ b a))

theorem gomi_neighOK_E7 : ∀ m ∈ [0, 1, 2, 3], gomiNeighOK Tag.E7 (ToralSign.natBits m) = true := by
  decide +kernel

theorem gomi_neighOK_E6 : ∀ m ∈ [0, 20, 2], gomiNeighOK Tag.E6 (ToralSign.natBits m) = true := by
  decide +kernel

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
