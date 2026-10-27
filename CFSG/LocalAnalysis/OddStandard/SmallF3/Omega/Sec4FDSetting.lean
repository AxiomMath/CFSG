module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

structure Sec4FDCover {G Pr : Type} [Group G] [Group Pr] (L : Subgroup G) (s : G)
    (X : Subgroup Pr) [X.Normal] (y : Pr) (ρ : ↥L →* ↥X) : Prop where
  cover : OddCentralCover ρ
  s_norm : s ∈ normalizer (L : Set G)
  s_sq : s * s = 1
  y_sq : y * y = 1
  equi : ∀ l l' : ↥L, (l' : G) = s * l * s⁻¹ →
    ((ρ l' : ↥X) : Pr) = y * ((ρ l : ↥X) : Pr) * y⁻¹

end CFSG.OddStandard.SmallF3.Omega
