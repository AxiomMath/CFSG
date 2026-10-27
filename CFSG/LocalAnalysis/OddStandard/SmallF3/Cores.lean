module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Blocks

public section

namespace CFSG.OddStandard.SmallF3

open Subgroup CFSG.Blueprint

@[expose] def SmallF3L33Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SmallF3Cyclic G L → ¬ Blueprint.Catalog G →
    LieModel (L ⧸ center L) .PSL 3 3 1 → False

@[expose] def SmallF3U33Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SmallF3Cyclic G L → ¬ Blueprint.Catalog G →
    LieModel (L ⧸ center L) .PSU 3 3 1 → False

@[expose] def SmallF3OmegaCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SmallF3Cyclic G L → ¬ Blueprint.Catalog G →
    SmallF3OmegaQuotient (L ⧸ center L) → False

end CFSG.OddStandard.SmallF3
