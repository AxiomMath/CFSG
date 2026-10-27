module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Inputs

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519

@[expose] def TabClass8Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    IsComponentIn K (X ⊓ Subgroup.centralizer ({t} : Set G)) → PatSp4 X K →
    ∀ P : Subgroup G, IsSylowTwoOf P X → t ∈ Subgroup.normalizer (P : Set G) →
      8 ≤ (Subgroup.centralizer ({t} : Set G)).relIndex P

@[expose] def TabClass8L5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    IsComponentIn K (X ⊓ Subgroup.centralizer ({t} : Set G)) → PatL5 X K →
    ∀ P : Subgroup G, IsSylowTwoOf P X → t ∈ Subgroup.normalizer (P : Set G) →
      8 ≤ (Subgroup.centralizer ({t} : Set G)).relIndex P

@[expose] def TabClass8HS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    IsComponentIn K (X ⊓ Subgroup.centralizer ({t} : Set G)) → PatHS X K t →
    ∀ P : Subgroup G, IsSylowTwoOf P X → t ∈ Subgroup.normalizer (P : Set G) →
      8 ≤ (Subgroup.centralizer ({t} : Set G)).relIndex P

structure Inputs2436Core : Prop where
  i32 : LemmaI32
  p121_3 : Prop121Three
  p121_5 : Prop121Five
  list115 : Lemma115_3_List
  threeRank : TabThreeRank
  ident : TabIdentA6

theorem Inputs2436Core.toInputs2436 (h : Inputs2436Core) (h8 : TabClass8) : Inputs2436 :=
  ⟨h.i32, h.p121_3, h.p121_5, h.list115, h.threeRank, h.ident, h8⟩

theorem tabClass8_of_split (h1 : TabClass8Sp4) (h2 : TabClass8L5) (h3 : TabClass8HS) : TabClass8 := by
  intro G _ _ X K t hq htN ht2 hXt hK hpat P hP htP
  rcases hpat with h | h | h
  · exact h1 G X K t hq htN ht2 hXt hK h P hP htP
  · exact h2 G X K t hq htN ht2 hXt hK h P hP htP
  · exact h3 G X K t hq htN ht2 hXt hK h P hP htP

end CFSG.QuasithinUnique.DoubleA3
