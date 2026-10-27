module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Setup
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.LocalAnalysis.RankThreeUC

@[expose] def NineTwelveOneSigmaStrong : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H F : Subgroup G) (q : ℕ),
    O1217.Setting1417 G M Q H F q → q ≠ 3 →
    ∀ L : Subgroup G, AGL81C.IsPComponentIn q L H → ¬ L ≤ M → AGL81C.IsTwoPrimeComponentIn L H

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
