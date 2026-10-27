module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Fact58Swap : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G) (B A : Subgroup G),
    Sec5RCtx G t L S z r B A →
      ∃ g : G, g⁻¹ * t * g = r ∧
        ∃ α : ℤˣ, InducesTypeSome (CFSG.conjugate L g) t 6 (-1) 1 α

end CFSG.OddStandard.SmallF3.Omega
