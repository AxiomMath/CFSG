module

public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G]

@[expose] def IsTwoNilpotent (X : Subgroup G) : Prop :=
  ∃ N : Subgroup G, N ≤ X ∧ (N.subgroupOf X).Normal ∧ Odd (Nat.card N) ∧
    ∃ k : ℕ, N.relIndex X = 2 ^ k

@[expose] def NoncyclicFaithful (T A : Subgroup G) : Prop :=
  IsElemAbelian 2 T ∧ 4 ≤ Nat.card T ∧ T ≤ normalizer (A : Set G) ∧
    T ⊓ centralizer (A : Set G) = ⊥

@[expose] def SylowInTightTwoNilpotent (T A : Subgroup G) : Prop :=
  ∃ X : Subgroup G, X ≤ T ⊔ A ∧ IsSylowOf 2 T X ∧ IsTwoNilpotent X ∧
    TightlyEmbedded (X.subgroupOf (T ⊔ A))

@[expose] def HypII (A : Type*) [Group A] : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (B T : Subgroup H), Nonempty (B ≃* A) →
    NoncyclicFaithful T B → SylowInTightTwoNilpotent T B →
      T ≤ B ⊔ centralizer (B : Set H)

@[expose] def oUpperTwo (X : Subgroup G) : Subgroup G :=
  closure {x | x ∈ X ∧ Odd (orderOf x)}

@[expose] def admResidual (X : Subgroup G) : Subgroup G :=
  sInf {Y : Subgroup G | Y ≤ X ∧ ∃ _ : (Y.subgroupOf X).Normal,
    Group.IsSolvable (X ⧸ Y.subgroupOf X) ∧
      ∀ S : Sylow 2 (X ⧸ Y.subgroupOf X), IsMulCommutative (S : Subgroup (X ⧸ Y.subgroupOf X))}

@[expose] def IsAdmissible (T A : Subgroup G) : Prop :=
  NoncyclicFaithful T A ∧ SylowInTightTwoNilpotent T A ∧
    (Nat.card T = 4 ∨ ∀ a ∈ A, T ⊓ normalizer (rightConjugate T a : Set G) ≤
      centralizer (rightConjugate T a : Set G)) ∧
    ∀ t ∈ T, t ≠ 1 →
      admResidual (oUpperTwo (A ⊓ centralizer ({t} : Set G))) ≤ centralizer (T : Set G)

structure Hyp31 {G : Type} [Group G] [Finite G] (A : Subgroup G) : Prop where
  standard : standardComponentIsStandard A
  hypII : HypII A
  oddCore : standardComponentOddCore G = ⊥
  rank : 1 < Open.pRank 2 (centralizer (A : Set G))
  not_normal : ¬ A.Normal

@[expose] def gammaOneOn (T B : Subgroup G) : Subgroup G :=
  ⨆ (U : Subgroup G) (_ : U ≤ T) (_ : U ≠ ⊥), B ⊓ normalizer (U : Set G)

@[expose] def Asc76HypII (A : Type*) [Group A] : Prop :=
  Open.IsQuasisimple A ∧ ∀ (H : Type) [Group H] [Finite H] (B Q T : Subgroup H),
    Nonempty (B ≃* A) → Q ≤ normalizer (B : Set H) → IsSylowOf 2 T Q → ¬ B ≤ gammaOneOn T B →
    IsElemAbelian 2 T → 4 ≤ Nat.card T → IsTwoNilpotent Q →
    TightlyEmbedded (Q.subgroupOf (Q ⊔ B)) → T ≤ B ⊔ centralizer (B : Set H)

@[expose] def Asc76Theorem2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), standardComponentOddCore G = ⊥ →
    standardComponentIsStandard A → Asc76HypII A → 1 < Open.pRank 2 (centralizer (A : Set G)) →
    ∀ R : Subgroup G, IsSylowOf 2 R (centralizer (A : Set G)) →
    ∀ g : G, g ∉ normalizer (A : Set G) → ∀ T : Subgroup G,
      IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)) →
      T ≠ ⊥ →
      (Nat.card R = 4 ∧ IsElemAbelian 2 R ∧
          ∃ g' : G, g' ∉ normalizer (A : Set G) ∧ ∃ T' : Subgroup G,
            IsSylowOf 2 T'
                (rightConjugate (centralizer (A : Set G)) g' ⊓ normalizer (A : Set G)) ∧
              IsSylowOf 2 T' (rightConjugate (centralizer (A : Set G)) g')) ∨
        (IsElemAbelian 2 R ∧ IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g) ∧
          ⁅T ⊓ normalizer (R : Set G), R⁆ = ⊥)

@[expose] def Lemma32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), Hyp31 A →
    ∀ R : Subgroup G, IsSylowOf 2 R (centralizer (A : Set G)) → IsElemAbelian 2 R

@[expose] def Lemma33Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), Hyp31 A →
    ∃ g : G, g ∉ normalizer (A : Set G) ∧ ∃ T : Subgroup G,
      IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)) ∧
        IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)

@[expose] def Lemma33One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), Hyp31 A →
    ∀ R : Subgroup G, IsSylowOf 2 R (centralizer (A : Set G)) →
    ∀ g : G, g ∉ normalizer (A : Set G) → ∀ T : Subgroup G,
      IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)) →
      T ≠ ⊥ → T ≤ normalizer (R : Set G) →
        Nat.card R = 4 ∨
          (IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g) ∧ ⁅T, R⁆ = ⊥)

@[expose] def Lemma33Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), Hyp31 A →
    ∀ R : Subgroup G, IsSylowOf 2 R (centralizer (A : Set G)) →
    ∀ g : G, g ∉ normalizer (A : Set G) → ∀ T : Subgroup G,
      IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)) →
      T ≠ ⊥ → T ≤ normalizer (R : Set G) →
      IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g) →
        T ≤ A ⊔ centralizer (A : Set G)

@[expose] def Section3Config : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), Hyp31 A →
    ∃ g : G, g ∉ normalizer (A : Set G) ∧ ∃ R T : Subgroup G,
      IsSylowOf 2 R (centralizer (A : Set G)) ∧
      IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g) ∧
      T ≤ normalizer (A : Set G) ∧ R ≤ normalizer (rightConjugate A g : Set G) ∧
      ⁅T, R⁆ = ⊥ ∧ SylowInTightTwoNilpotent T A ∧
      SylowInTightTwoNilpotent R (rightConjugate A g)

end CFSG.ComponentClassification.AS76b
