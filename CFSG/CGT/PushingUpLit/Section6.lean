module

public import CFSG.CGT.PushingUpLit.Defs

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.Assembly
open scoped commutatorElement Pointwise

@[expose] def AschbacherSixTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ (Y V : Subgroup G), InClassX ↥Y → V.Normal → IsElementaryAbelian 2 V →
      ¬ Y ≤ Subgroup.centralizer (V : Set G) →
      (∃ P : Subgroup G, IsPGroup 2 P ∧ ¬ P ≤ Subgroup.centralizer (V : Set G) ∧
        Y ≤ Subgroup.normalizer ((P ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ∧
        (Y.subgroupOf (Subgroup.normalizer
          ((P ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))).IsSubnormal) →
      ∀ R : Subgroup G, IsSylowOf 2 R (centralizerModCore Y) →
        (Y = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆ ∨
          (Y ≤ Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ∧
            (Y.subgroupOf (Subgroup.normalizer ((jIn R : Subgroup G) : Set G))).IsSubnormal)) →
        ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧ InClassX ↥X ∧ Arrow Y X ∧
          (Y = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆ → X = ⁅jIn (⊤ : Subgroup G), X⁆) ∧
          (¬ Y = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆ → Y = X)

@[expose] def AschbacherSixThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ Y : Subgroup G, InClassXG Y →
      ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧ InClassX ↥X ∧ Arrow Y X ∧
        (X = Y ∨ X = ⁅jIn (⊤ : Subgroup G), X⁆)

@[expose] def AschbacherSixSixteen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ (Y : Subgroup G) (T : Sylow 2 G), InClassX ↥Y → Y = ⁅jIn (T : Subgroup G), Y⁆ →
      ∀ R : Subgroup G, IsSylowOf 2 R (centralizerModCore Y) →
        ∀ U₀ : Subgroup G, ⁅oTwoIn Y, Y⁆ ≤ U₀ → U₀ ≤ (T : Subgroup G) →
          Y ≤ Subgroup.normalizer (U₀ : Set G) →
          (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G))).IsSubnormal →
          ∀ S : Subgroup G, IsSylowOf 2 S (Subgroup.normalizer (R : Set G)) →
            IsSylowOf 2 (S ⊓ Subgroup.normalizer (Y : Set G)) (Subgroup.normalizer (Y : Set G)) →
            ⁅omegaOneCenterIn S, Y⁆ ≠ ⊥ →
            ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧ InClassX ↥X ∧ Arrow Y X

@[expose] def AschbacherEightOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → CFSG.Assembly.IsCharTwoType G →
    ∀ X : Subgroup G, IsMaximalInClassXG X → ∀ N : Subgroup G,
      N ∈ maximalTwoLocalsContaining (X : Set G) → (X.subgroupOf N).IsSubnormal

@[expose] def blocksStar {G : Type} [Group G] [Finite G] (T : Subgroup G) : Set (Subgroup G) :=
  {Y | IsBlockInX Y ∧ ∀ g : G, ¬ Y ≤ conjugate (characteristicCoreStar T) g}

@[expose] def AschbacherLocalFactorization : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ T : Sylow 2 G,
      (⨆ (Y : Subgroup G) (_ : Y ∈ blocksStar (T : Subgroup G)), Y) ⊔
        characteristicCoreStar (T : Subgroup G) = ⊤

theorem AschbacherLocalFactorization.exists_not_le (h : AschbacherLocalFactorization)
    {G : Type} [Group G] [Finite G] (hK : KProper InCatalog G) (hchar : IsCharacteristicP 2 G)
    (T : Sylow 2 G) {M' : Subgroup G} (hM' : characteristicCoreStar (T : Subgroup G) ≤ M')
    (hne : M' ≠ ⊤) : ∃ Y ∈ blocksStar (T : Subgroup G), ¬ Y ≤ M' := by
  by_contra hall
  have hall' : ∀ Y ∈ blocksStar (T : Subgroup G), Y ≤ M' := fun Y hY =>
    not_not.mp fun hn => hall ⟨Y, hY, hn⟩
  refine hne (top_le_iff.mp ?_)
  rw [← h G hK hchar T]
  exact sup_le (iSup_le fun Y => iSup_le fun hY => hall' Y hY) hM'

end CFSG.CGT.PushingUpLit
