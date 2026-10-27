module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Config

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG

structure H2Two (G : Type*) [Group G] (t v : G) (J S₁ : Subgroup G) : Prop where
  comp₁ : IsComponent S₁
  comp₀ : IsComponent ⁅J, J⁆
  ne : S₁ ≠ ⁅J, J⁆
  comps : ∀ M : Subgroup G, IsComponent M → M = S₁ ∨ M = ⁅J, J⁆
  layer_eq : layer G = S₁ ⊔ ⁅J, J⁆
  V_le : kleinV t v ≤ S₁
  inf_le : S₁ ⊓ centralizer ({t} : Set G) ≤ kleinV t v

@[expose] def jOne {G : Type*} [Group G] (t : G) (S₁ : Subgroup G) : Subgroup G :=
  centralizer ({t} : Set G) ⊓ centralizer (S₁ : Set G)

end CFSG.EvenSporadicStandard.HSStd.InvCent
