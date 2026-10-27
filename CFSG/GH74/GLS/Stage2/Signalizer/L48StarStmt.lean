module

public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L48

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def Star48 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (t : G) (ht : t ∈ Cen z) (p : ℕ), p.Prime → p ≠ 2 →
      IVK.IsFourSubgroup (zpowers z ⊔ zpowers t) → zpowers z ⊔ zpowers t ≤ S →
      (∀ s ∈ S, ∀ u ∈ zpowers z ⊔ zpowers t, s * u * s⁻¹ ∈ zpowers z ⊔ zpowers t) →
      ∀ Y : Subgroup (CentralizerBar z), IsPGroup p ↥Y →
        (∀ c : CentralizerBar z, c * toBar z ⟨t, ht⟩ = toBar z ⟨t, ht⟩ * c →
          c ∈ normalizer (Y : Set (CentralizerBar z))) →
        ⁅Y, zpowers (toBar z ⟨t, ht⟩)⁆ = Y → Y = ⊥

end CFSG.GH74.GLS.Stage2.Signalizer.L48
