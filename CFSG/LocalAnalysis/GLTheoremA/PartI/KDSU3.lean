module

public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def KDSU3 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSUThreeTwoPow L →
    ∀ E T : Subgroup (MulAut L), IsElemAbelian 3 E → T ≠ ⊥ → IsPGroup 2 T →
      E ≤ Subgroup.normalizer (T : Set (MulAut L)) → Nat.card E ≤ 3

end CFSG.LocalAnalysis.GLTheoremA
