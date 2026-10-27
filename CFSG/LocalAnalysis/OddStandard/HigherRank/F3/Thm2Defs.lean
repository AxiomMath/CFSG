module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Defs

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit

@[expose] def IdentGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    ∀ w v : G, orderOf w = 2 → v * v = 1 → v ∉ zpowers w → v ∈ centralizer {w} →
    ∀ J : Subgroup G, IsTwoComponentIn J (centralizer {w} ⊓ centralizer {v}) →
      IsMTypeSchur 3 ↥J → ClassBShape ↥J → w ∈ J →
    ∀ K : Subgroup G,
      K = ComponentClassification.GSThmB.conjClosure J
        (ComponentClassification.GSThmB.layerIn (centralizer {w})) → J ≤ K →
      IsTwoComponentIn K (centralizer {w}) → w ∈ K → ¬ IsMTypeSchur 3 ↥K →
      K.map (MulAut.conj v).toMonoidHom = K → False

@[expose] def Theorem2ClassB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    ∀ W : Subgroup G, (∀ a ∈ W, a * a = 1) → Nat.card ↥W = 4 →
    ∀ z₁ ∈ W, ∀ z₂ ∈ W, z₁ ≠ 1 → z₂ ≠ 1 → z₁ ≠ z₂ →
    ∀ L₁ L₂ : Subgroup G, IsTwoComponentIn L₁ (centralizer (W : Set G)) →
      IsTwoComponentIn L₂ (centralizer (W : Set G)) → z₁ ∈ L₁ → z₂ ∈ L₂ →
      IsMTypeSchur 3 ↥L₁ → ClassBShape ↥L₁ → False

end CFSG.OddStandard.HigherRank.F3
