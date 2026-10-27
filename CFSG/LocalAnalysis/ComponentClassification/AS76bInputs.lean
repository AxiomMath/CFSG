module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G]

@[expose] def oddCoreIn (Q : Subgroup G) : Subgroup G :=
  (CFSG.Assembly.oddCore Q).map Q.subtype

@[expose] def twoPrimeLayerIn (Q : Subgroup G) : Subgroup G :=
  ((CFSG.layer (Q ⧸ CFSG.Assembly.oddCore Q)).comap
    (QuotientGroup.mk' (CFSG.Assembly.oddCore Q))).map Q.subtype

@[expose] def oUpperTwoPrime (X : Subgroup G) : Subgroup G :=
  closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1}

@[expose] def NormalIn (M N : Subgroup G) : Prop :=
  M ≤ N ∧ (M.subgroupOf N).Normal

@[expose] def Asc75Theorem4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Q : Subgroup G), TightlyEmbedded Q →
    twoPrimeLayerIn Q ≠ oddCoreIn Q →
    NormalIn (twoPrimeLayerIn Q) (twoPrimeLayerIn (⊤ : Subgroup G)) ∨
      (Open.pRank 2 (twoPrimeLayerIn Q) = 1 ∧
        (1 < Open.pRank 2 Q → ∀ g : G, g ∉ normalizer (Q : Set G) →
          Even (Nat.card (rightConjugate Q g ⊓ normalizer (Q : Set G) : Subgroup G)) →
          ∃ S : Subgroup G, IsSylowOf 2 S (rightConjugate Q g) ∧
            S ≤ normalizer (Q : Set G))) ∨
      ∃ g : G, g ∉ normalizer (Q : Set G) ∧ ∃ T : Subgroup G,
        IsSylowOf 2 T (rightConjugate Q g) ∧ T ≤ normalizer (Q : Set G) ∧
        ∃ n : ℕ, 2 ≤ n ∧ ∃ φ : oUpperTwoPrime (Q ⊔ T) →*
            Multiplicative (Fin n → ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
          Function.Surjective φ ∧ φ.ker = (oddCoreIn Q).subgroupOf (oUpperTwoPrime (Q ⊔ T))

@[expose] def Asc08Lemma34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), Hyp31 A →
    normalClosure (A : Set G) = CFSG.generalizedFitting G ∧
      IsSimpleGroup (CFSG.generalizedFitting G)

end CFSG.ComponentClassification.AS76b
