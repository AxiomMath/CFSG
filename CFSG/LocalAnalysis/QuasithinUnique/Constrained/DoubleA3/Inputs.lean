module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519

@[expose] def TabClass8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    IsComponentIn K (X ⊓ Subgroup.centralizer ({t} : Set G)) →
    (PatSp4 X K ∨ PatL5 X K ∨ PatHS X K t) →
    ∀ P : Subgroup G, IsSylowTwoOf P X → t ∈ Subgroup.normalizer (P : Set G) →
      8 ≤ (Subgroup.centralizer ({t} : Set G)).relIndex P

@[expose] def TabIdentA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    (∃ z : G, Lemma115Cases X z) → t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 →
    ⁅X, Subgroup.zpowers t⁆ = X →
    IsComponentIn K (X ⊓ Subgroup.centralizer ({t} : Set G)) → IsA6 K →
      PatSp4 X K ∨ PatL5 X K ∨ PatHS X K t ∨ PatA8 X K t

theorem TabIdent.toA6 (h : TabIdent) : TabIdentA6 := by
  intro G _ _ X K t hq hex htN ht2 hXt hK hA6
  exact (h G X K t hq hex htN ht2 hXt hK (Or.inr (Or.inr hA6))).2.2.2.2 hA6

structure Inputs2436 : Prop where
  i32 : LemmaI32
  p121_3 : Prop121Three
  p121_5 : Prop121Five
  list115 : Lemma115_3_List
  threeRank : TabThreeRank
  ident : TabIdentA6
  class8 : TabClass8

end CFSG.QuasithinUnique.DoubleA3
