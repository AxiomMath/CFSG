module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4Gomi

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

variable {G : Type} [Group G]

@[expose] def Data.nclL (d : Data G) (K₀ : Subgroup G) : Subgroup G :=
  ⨆ l ∈ d.L, K₀.map (MulAut.conj l).toMonoidHom

structure Data.IsUnitaryFactor (d : Data G) (K₀ : Subgroup G) : Prop where
  lieModel : CFSG.Blueprint.LieModel K₀ .PSU 4 2 1
  K_eq : d.K = K₀ ⊔ K₀.map (MulAut.conj d.t).toMonoidHom
  comm : ⁅K₀, K₀.map (MulAut.conj d.t).toMonoidHom⁆ = ⊥
  inf : K₀ ⊓ K₀.map (MulAut.conj d.t).toMonoidHom = ⊥

@[expose] def UnitaryCommutation : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (d : Data G), d.Hyp → d.KUnitary →
    ∀ K₀ : Subgroup G, d.IsUnitaryFactor K₀ →
      ⁅d.nclL K₀, (d.nclL K₀).map (MulAut.conj d.t).toMonoidHom⁆ = ⊥

structure Data.UnitaryProductData (d : Data G) (A : Subgroup G) : Prop where
  perfect : ⁅A, A⁆ = A
  ne_bot : A ≠ ⊥
  comm : ⁅A, A.map (MulAut.conj d.t).toMonoidHom⁆ = ⊥
  L_le : d.L ≤ A ⊔ A.map (MulAut.conj d.t).toMonoidHom
  normalizer_R : normalizer (d.R : Set G) ≤
    normalizer ((A ⊔ A.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G)

@[expose] def UnitaryProduct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (d : Data G), d.Hyp → d.KUnitary →
    ∃ A : Subgroup G, d.UnitaryProductData A

theorem Data.KUnitary.exists_isUnitaryFactor {d : Data G} (h : d.KUnitary) :
    ∃ K₀ : Subgroup G, d.IsUnitaryFactor K₀ := by
  obtain ⟨K₀, hm, hK, hc, hi⟩ := h.swap
  exact ⟨K₀, ⟨hm, hK, hc, hi⟩⟩

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
