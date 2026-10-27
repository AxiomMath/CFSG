module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3

@[expose] def Comp25Component : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg2 G T M H S L →
    ∀ x : G, x ∈ T → x ∈ Subgroup.normalizer (S : Set G) →
      ¬ conjR (blockU L) x ≤ s2Q1 S L → A5s2B T M H S L x →
        ∃ K : Subgroup G, IsComponentIn K (Subgroup.normalizer (s2Phi S L : Set G)) ∧ L ≤ K ∧
          (K.subgroupOf (Subgroup.normalizer (s2Phi S L : Set G))).Normal

@[expose] def Comp25List : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg2 G T M H S L →
    ∀ x : G, x ∈ T → x ∈ Subgroup.normalizer (S : Set G) →
      ¬ conjR (blockU L) x ≤ s2Q1 S L → A5s2B T M H S L x →
        ∀ K : Subgroup G, IsComponentIn K (Subgroup.normalizer (s2Phi S L : Set G)) → L ≤ K →
          Kc3Group (↥K ⧸ Subgroup.center ↥K) ∧ IsPGroup 2 ↥(Subgroup.center ↥K)

@[expose] def TabKc3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L : Subgroup G) (z : G), CFSG.IsQuasisimple ↥K →
    Lemma115Cases K z → L ≤ K → IsShort2 L → IsAltType L 5 →
      Kc3Group (↥K ⧸ Subgroup.center ↥K) ∧ IsPGroup 2 ↥(Subgroup.center ↥K)

end CFSG.QuasithinUnique.A5
