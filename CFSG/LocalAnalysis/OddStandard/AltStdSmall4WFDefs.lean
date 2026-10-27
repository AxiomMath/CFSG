module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Defs

public section

namespace CFSG.OddStandard.AltStdSmall4

open Subgroup

@[expose] def Sec4WreathFalseBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (T : Subgroup G),
      ¬ IsASmall L n z → HData θ c.hn8 z T → WreathStruct z T → False

end CFSG.OddStandard.AltStdSmall4
