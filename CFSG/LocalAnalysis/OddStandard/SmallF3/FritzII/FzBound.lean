module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Hyp

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open CFSG.Blueprint

@[expose] def Harris1981Bound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (L : Subgroup G) (t : G),
    HarrisU33.Hyp G t L → CFSG.Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
      2 ^ 11 ∣ Nat.card G → False

end CFSG.OddStandard.SmallF3.FritzII
