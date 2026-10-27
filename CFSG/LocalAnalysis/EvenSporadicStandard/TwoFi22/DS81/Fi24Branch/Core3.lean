module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.RNormal

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {t z : G}

structure Core3 (E : Subgroup G) (t z : G) : Prop extends Core2 E t z where
  rnorm : ∀ n ∈ CNz E z, ∀ x ∈ Rg t z, n * x * n⁻¹ ∈ Rg t z

theorem core3 (c : Core2 E t z) : Core3 E t z := ⟨c, R_normal_CNz c⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
