module

public import CFSG.LargeExtraspecial.DWTransGL

public section

namespace CFSG.LargeExtraspecial.DW

open Subgroup

variable {G : Type*} [Group G] [Finite G]

@[expose] def SpConfig (S : Setting G) (A : Subgroup G) (hM : S.M ≤ normalizer (A : Set G)) :
    Prop :=
  ∃ ω : LinearMap.BilinForm (ZMod 2) (S.clSub A), ω.Nondegenerate ∧ ω.IsAlt ∧
    ∀ f : S.clSub A ≃ₗ[ZMod 2] S.clSub A,
      f ∈ (resAt S A hM).range ↔ ∀ u v, ω (f u) (f v) = ω u v

end CFSG.LargeExtraspecial.DW
