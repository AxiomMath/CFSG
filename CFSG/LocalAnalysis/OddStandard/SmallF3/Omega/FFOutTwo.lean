module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6Aut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem ff_out_two_six_plus :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
      ∀ x : G, x ∈ normalizer (L : Set G) → Odd (orderOf x) → InnerOn L x :=
  fun _ _ _ _ hL => asc82OddInner_of_isOm6P hL

theorem ff_out_two_six_minus :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
      ∀ x : G, x ∈ normalizer (L : Set G) → Odd (orderOf x) → InnerOn L x :=
  fun _ _ _ _ hL => asc82OddInner_of_isOm6M hL

end CFSG.OddStandard.SmallF3.Omega
