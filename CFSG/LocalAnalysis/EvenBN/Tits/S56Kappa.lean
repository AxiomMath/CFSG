module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56V1
public import CFSG.Yardstones.M41b0c98b3153.Definitions

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup

namespace Data

variable {G : Type} [Group G] [Finite G]


@[expose] def S56Kappa (d : Data G) : Prop :=
  ∀ x ∈ d.s56V ⊓ d.N, ∀ f ∈ d.F, x * f * x⁻¹ * f⁻¹ ∈ d.s56U11

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
