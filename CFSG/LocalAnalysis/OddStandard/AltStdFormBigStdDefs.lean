module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction

public section

namespace CFSG.OddStandard.AltStdSec

@[expose] def AltStdFormBigStd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G),
    CFSG.EvenSporadicStandard.StdHyp G L → ∀ n : ℕ, 12 ≤ n →
      Nonempty (L ≃* alternatingGroup (Fin n)) → False

end CFSG.OddStandard.AltStdSec
