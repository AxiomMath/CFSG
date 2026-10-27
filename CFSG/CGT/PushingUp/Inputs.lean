module

public import CFSG.CGT.PushingUp.Defs
public import CFSG.GH74.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUp

open CFSG CFSG.RankThree.PartOne
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open scoped Pointwise

@[expose] def ThreeTwoConclusion (G : Type) [Group G] [Finite G] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ (Nonempty (G ≃* projSL 2 (GaloisField 2 n)) ∨
    Nonempty (G ≃* projSU 3 2 n) ∨ Nonempty (G ≃* projSL 3 (GaloisField 2 n)) ∨
    Nonempty (G ≃* projSp 2 (GaloisField 2 n)))) ∨
  (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
    Nonempty (G ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group)) ∨
  ∀ P : Subgroup G, IsPGroup 2 P →
    ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P

@[expose] def AschbacherTheoremOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.IsCharTwoType G → ∀ X : Subgroup G,
    InOmega X → (∀ Y : Subgroup G, InOmega Y → Arrow X Y → Y = X) →
      ∃ M : Subgroup G, maximalTwoLocalsContaining (X : Set G) = {M}

@[expose] def AschbacherTheoremTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → CFSG.Assembly.IsCharTwoType G →
    ∀ (L M : Subgroup G), InClassX ↥L → IsMaximalTwoLocal M → L ≤ M →
      (L.subgroupOf M).IsSubnormal → maximalTwoLocalsContaining (L : Set G) = {M} →
        ∀ n : ℕ, 2 ≤ n → IsNaturalSLTwoModule ↥L n →
          Nonempty (G ≃* projSL 3 (GaloisField 2 n)) ∨
            Nonempty (G ≃* projSp 2 (GaloisField 2 n)) ∨
              (n = 2 ∧ CFSG.GH74.sectionalTwoRank G = 4)

@[expose] def SolomonAlternatingBlock : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → CFSG.Assembly.IsCharTwoType G →
    ∀ (M X : Subgroup G), IsMaximalTwoLocal M → X ≤ M → (X.subgroupOf M).IsSubnormal →
      InClassX ↥X → (∃ n : ℕ, 1 ≤ n ∧ IsNaturalAltModule ↥X n) →
        maximalTwoLocalsContaining (X : Set G) = {M} → CFSG.GH74.SectionalTwoRankLE G 4

@[expose] def AschbacherLocalPushingUp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K T T₁ T₂ : Subgroup G),
    pCore 2 ↥K ≠ ⊥ → IsCharacteristicP 2 ↥K → IsSylowOf 2 T K →
    T₁ ≤ pushingUpS T → (T₁.subgroupOf (pushingUpS T)).Characteristic →
    T₂ ≤ omegaOneCenterIn T → PushingUpWhenever (pushingUpS T) T₁ T₂ →
    (Subgroup.centralizer (T₂ : Set G) ⊓ K) ⊔ (Subgroup.normalizer (T₁ : Set G) ⊓ K) ≠ K →
      ∃ (n : ℕ) (L : Fin n → Subgroup G), (∀ i, IsBlockOfInX K (L i)) ∧
        blockProduct ((Subgroup.centralizer (T₂ : Set G) ⊓ K) ⊔
          (Subgroup.normalizer (T₁ : Set G) ⊓ K)) L = (K : Set G)

@[expose] def AschbacherLocalBlockExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K T T₁ T₂ : Subgroup G),
    pCore 2 ↥K ≠ ⊥ → IsCharacteristicP 2 ↥K → IsSylowOf 2 T K →
    T₁ ≤ pushingUpS T → (T₁.subgroupOf (pushingUpS T)).Characteristic →
    T₂ ≤ omegaOneCenterIn T → PushingUpWhenever (pushingUpS T) T₁ T₂ →
    (Subgroup.centralizer (T₂ : Set G) ⊓ K) ⊔ (Subgroup.normalizer (T₁ : Set G) ⊓ K) ≠ K →
      ∃ L : Subgroup G, IsBlockOfInX K L

end CFSG.CGT.PushingUp
