module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.C41PfCorr

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

@[expose] def C134Case4F_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) → C134CorrLocal.IsC134Case4Corr G₀ R L →
    ∀ c ∈ c134CQ G₀ L, ∀ y ∈ c134Q G₀ L,
      (∀ x ∈ c134Q G₀ L, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.zpowers c) → y ∈ centerOf (c134Q G₀ L)

end CFSG.Quasithin.H13.A5
