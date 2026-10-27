module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Defs

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup

@[expose] def Sec3CentZNormalizes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G) (E F : Subgroup G) (x : G)
    (Zs P T Q B₀ : Subgroup G) (z y : G) (D J U V₀ V Q₀ : Subgroup G),
    Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ →
      centralizer (Zs : Set G) ≤ normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G)

end CFSG.ComponentClassification.AS81
