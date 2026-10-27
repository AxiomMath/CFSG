module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalM12
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltHypIISix
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinA6
public import CFSG.Permutation.AlternatingAutomorphism

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherTightEmbedding

structure Case310Local {G : Type} [Group G] (A R : Subgroup G) (g : G) (T V₀ : Subgroup G) :
    Prop where
  g_not_mem : g ∉ normalizer (A : Set G)
  sylowT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)
  T_le_normalizer : T ≤ normalizer (A : Set G)
  T_le_centralizer : T ≤ centralizer (R : Set G)
  sylowV₀ : IsSylowOf 2 V₀ A
  V₀_le : V₀ ≤ rightConjugate A g
  elem : IsElemAbelian 2 (R ⊔ T)
  card : Nat.card (R ⊔ T : Subgroup G) = 16
  inf_A : (R ⊔ T) ⊓ A = V₀
  inf_Ag : (R ⊔ T) ⊓ rightConjugate A g = V₀
  spread : ∀ x : G, rightConjugate R x ≤ R ⊔ T → rightConjugate R x ⊓ V₀ = ⊥
  cover : ∀ v ∈ R ⊔ T, v ∉ V₀ → ∃ x : G, rightConjugate R x ≤ R ⊔ T ∧ v ∈ rightConjugate R x
  noRoot : ∀ x : G, V₀ ⊓ rightConjugate (centralizer (A : Set G)) x = ⊥
  trans2 : ∀ x₁ x₂ x₁' x₂' : G, rightConjugate R x₁ ≤ R ⊔ T → rightConjugate R x₂ ≤ R ⊔ T →
    rightConjugate R x₁' ≤ R ⊔ T → rightConjugate R x₂' ≤ R ⊔ T →
    rightConjugate R x₁ ≠ rightConjugate R x₂ → rightConjugate R x₁' ≠ rightConjugate R x₂' →
    ∃ n ∈ normalizer ((R ⊔ T : Subgroup G) : Set G),
      rightConjugate (rightConjugate R x₁) n = rightConjugate R x₁' ∧
        rightConjugate (rightConjugate R x₂) n = rightConjugate R x₂'

@[expose] def Asc08Lemma310Local : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    standardComponentOddCore G = ⊥ → Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin 5)) →
    Odd (Nat.card (center ↥A)) → ∀ R : Subgroup G, IsSylowOf 2 R (centralizer (A : Set G)) →
    (∀ x : G, ¬ rightConjugate R x ≤ A) → rankTwoX A ⊔ R = ⊤ →
    ∀ (g : G) (T V₀ : Subgroup G), Case310Local A R g T V₀ →
      NativeSporadic.IsSporadic (rankTwoX A) .J2 ∨
        (NativeSporadic.IsSporadic (rankTwoX A) .M12 ∧
          ∃ t : G, t ^ 2 = 1 ∧ t ∈ normalizer (A : Set G) ∧ t ∈ normalizer (R : Set G) ∧
            ¬ ∃ a ∈ A, ∀ y ∈ A, t * y * t⁻¹ = a * y * a⁻¹)

theorem hypIIAlt5 :
    ∀ (A : Type) [Group A], commutator A = ⊤ →
      Nonempty (A ⧸ center A ≃* alternatingGroup (Fin 5)) → AS76b.HypII A := fun _ _ hA ⟨e⟩ =>
  RankTwoAlt.hypII_of_alternating_ge_five le_rfl hA e

end CFSG.ComponentClassification.RankTwoClassical
