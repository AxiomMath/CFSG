module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22PartThree
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22PartSix
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Defs

public section

namespace CFSG.ComponentClassification.Asc76

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

namespace Lemma22

@[expose] def PartTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K J T R : Subgroup G), TightlyEmbedded K →
    TightlyEmbedded J → Odd (Nat.card (K ⊓ J : Subgroup G)) →
    (Nat.card K).factorization 2 = (Nat.card J).factorization 2 →
    IsSylowOf 2 T (J ⊓ normalizer (K : Set G)) → T ≠ ⊥ → IsSylowOf 2 R K →
    T ≤ normalizer (R : Set G) → 1 < Open.pRank 2 K → 1 < Open.pRank 2 J →
    let W : Subgroup G := ⨆ (k : G) (_ : k ∈ K) (_ : rightConjugate T k ≤ R ⊔ T),
      rightConjugate T k
    T ≠ W → IsCyclic T → IsDihedralTwoGroup R ∧
      (IsDihedralTwoGroup (R ⊔ T) ∨ IsWreathedTwoGroup (R ⊔ T))

theorem partTwo : PartTwo := by
  intro G _ _ K J T R hK hJ hKJ hfac hT hT1 hR hTR hmK _ W hW hcyc
  exact isDihedral_and_of_isCyclic hK hJ hKJ hfac hT hT1 hR hTR hmK hW hcyc

theorem partSix :
    ∀ (G : Type) [Group G] [Finite G] (K J T R : Subgroup G), TightlyEmbedded K →
      TightlyEmbedded J → Odd (Nat.card (K ⊓ J : Subgroup G)) →
      (Nat.card K).factorization 2 = (Nat.card J).factorization 2 →
      IsSylowOf 2 T (J ⊓ normalizer (K : Set G)) → T ≠ ⊥ → IsSylowOf 2 R K →
      T ≤ normalizer (R : Set G) → 1 < Open.pRank 2 K → 1 < Open.pRank 2 J →
      let W : Subgroup G := ⨆ (k : G) (_ : k ∈ K) (_ : rightConjugate T k ≤ R ⊔ T),
        rightConjugate T k
      let NRT : Subgroup G := R ⊓ normalizer (T : Set G)
      ¬ IsElemAbelian 2 T → T ≠ W →
        W = T ⊔ NRT ∧
        (∀ E : Subgroup G, NRT ≤ E → E ≤ R → (∀ x ∈ E, x ^ 2 ∈ NRT) →
          (∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ NRT) → NRT.relIndex E ≤ 2) ∧
        ∀ r ∈ R, r ∉ NRT → r ^ 2 ∈ NRT → ∀ x ∈ NRT, r * x * r⁻¹ = x⁻¹ := by
  intro G _ _ K J T R hK hJ hKJ hfac hT hT1 hR hTR _ _ W NRT hel hW
  exact weakClosure_eq_and hK hJ hKJ hfac hT hT1 hR hTR hel hW

end Lemma22

theorem asc76Lemma22_of (h3 : Theorem3Statement) (h2 : Lemma22.PartTwo) :
    Asc76Lemma22 := by
  have h6 := Lemma22.partSix
  intro G _ _ K J T R hK hJ hKJ hfac hT hT1 hR hTR hmK hmJ
  exact ⟨⟨Lemma22.card_inf_normalizer hK hJ hKJ hfac hT hT1 hR hTR,
      Lemma22.nonempty_inf_normalizer_mulEquiv hK hJ hKJ hfac hT hT1 hR hTR⟩,
    h2 G K J T R hK hJ hKJ hfac hT hT1 hR hTR hmK hmJ,
    Lemma22.normalIn_or_exists_or_isCyclic h3 hK hJ hKJ hfac hT hT1 hR hTR,
    fun hTJ => Lemma22.commutator_le_or_isElemAbelian h3 hK hJ hKJ hfac hT hT1 hR hTR hmJ hTJ,
    fun hTJ => Lemma22.isMulCommutative hK hJ hKJ hfac hT hT1 hR hTR hTJ,
    h6 G K J T R hK hJ hKJ hfac hT hT1 hR hTR hmK hmJ,
    Lemma22.inf_normalizer_normal h3 hK hJ hKJ hfac hT hT1 hR hTR hmK⟩

theorem asc76Lemma22 (h3 : Theorem3Statement) : Asc76Lemma22 :=
  asc76Lemma22_of h3 Lemma22.partTwo

end CFSG.ComponentClassification.Asc76
