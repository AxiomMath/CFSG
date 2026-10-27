module

public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L48

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def Lemma4_8w : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    TypeOneCase G k →
    ∀ (t : G) (H X : Subgroup G) (p : ℕ), IVK.IsFourSubgroup (zpowers z ⊔ zpowers t) →
      zpowers z ⊔ zpowers t ≤ S → (∀ s ∈ S, ∀ u ∈ zpowers z ⊔ zpowers t, s * u * s⁻¹ ∈ zpowers z ⊔ zpowers t) →
      centralizer ({t} : Set G) ≤ H → t ∈ zStar H → Sig4Sub G z H p X →
      (∀ s ∈ S ⊓ centralizer (((zpowers z ⊔ zpowers t : Subgroup G)) : Set G), s ∈ normalizer (X : Set G)) →
      X ≤ Op p H

end CFSG.GH74.GLS.Stage2.Signalizer.L48
