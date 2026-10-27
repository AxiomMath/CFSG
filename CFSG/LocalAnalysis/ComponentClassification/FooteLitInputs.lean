module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitMaximal

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type*} [Group G]

@[expose] def twoLayerIn (Y : Subgroup G) : Subgroup G :=
  (pLayer ↥Y 2).map Y.subtype

@[expose] def IsTwoComponentIn (K Y : Subgroup G) : Prop :=
  K ≤ Y ∧ IsPComponent 2 (K.subgroupOf Y)

@[expose] def oddCoreIn (H : Subgroup G) : Subgroup G :=
  (pPrimeCore 2 ↥H).map H.subtype

@[expose] def oddResidualIn (H : Subgroup G) : Subgroup G :=
  closure {g : G | g ∈ H ∧ ∃ k : ℕ, orderOf g = 2 ^ k}

@[expose] def oddTwoCoreIn (H : Subgroup G) : Subgroup G :=
  ((pCore 2 (↥H ⧸ pPrimeCore 2 ↥H)).comap (QuotientGroup.mk' (pPrimeCore 2 ↥H))).map H.subtype

@[expose] def IsSolomonMember (L : Subgroup G) : Prop :=
  ⁅L, L⁆ = L ∧ ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ coreActionKernel L ∧
    IsTwoComponentIn
      (oddResidualIn (oddCoreIn (centralizer (T : Set G)) ⊔ (L ⊓ centralizer (T : Set G))))
      (centralizer (T : Set G))

@[expose] def SolomonLt (L K : Subgroup G) : Prop :=
  IsSolomonMember L ∧ IsSolomonMember K ∧ ∃ T : Subgroup G, IsPGroup 2 T ∧
    T ≤ coreActionKernel L ∧
    IsTwoComponentIn K (conjClosure (twoLayerIn (L ⊓ centralizer (T : Set G)))
      (twoLayerIn (centralizer (T : Set G))))

@[expose] def SolomonLink (L K : Subgroup G) : Prop :=
  Nonempty (L ⧸ Open.fusionZStar L ≃* K ⧸ Open.fusionZStar K) ∧ (SolomonLt L K ∨ SolomonLt K L)

@[expose] def SolomonEquiv (L K : Subgroup G) : Prop :=
  IsSolomonMember L ∧ Relation.ReflTransGen SolomonLink L K

@[expose] def IsSolomonMaximal (L : Subgroup G) : Prop :=
  IsSolomonMember L ∧
    ∀ K K₁ : Subgroup G, SolomonEquiv L K → SolomonLt K K₁ → SolomonEquiv L K₁

@[expose] def IsSolomonWide (L : Subgroup G) : Prop :=
  IsSolomonMember L ∧ ∀ K : Subgroup G, SolomonEquiv L K → 2 ≤ CFSG.pRank 2 ↥K

@[expose] def solomonKStar (G : Type*) [Group G] : Set (Subgroup G) :=
  {L | IsSolomonMaximal L ∧ IsSolomonWide L}

@[expose] def solomonKStarOf (H : Subgroup G) : Subgroup G :=
  ⨆ (K : Subgroup G) (_ : IsTwoComponentIn K H ∧ K ∈ solomonKStar G), K

@[expose] def HasStronglyEmbedded (K : Type*) [Group K] : Prop :=
  ∃ M : Subgroup K, CFSG.IsStronglyEmbedded M

@[expose] def IsTwoDisconnected (K : Type*) [Group K] : Prop :=
  ∃ B C : Subgroup K, IsKleinFour B ∧ IsKleinFour C ∧
    ¬ Relation.ReflTransGen
      (fun B C : Subgroup K => IsKleinFour B ∧ IsKleinFour C ∧ B ≤ centralizer (C : Set K)) B C

@[expose] def IsKBalanced (N : Subgroup G) : Prop :=
  ∃ (r : ℕ) (K : Fin r → Subgroup G), Function.Injective K ∧
    (∀ J : Subgroup G, (IsTwoComponentIn J N ∧ J ∈ solomonKStar G) ↔ ∃ i, K i = J) ∧
    ∃ h : 2 ≤ r, (∀ i j, i ≠ j → ⁅K i, K j⁆ ≤ oddCoreIn N) ∧
      (∃ i, 3 ≤ CFSG.pRank 2 ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (K i))) ∧
      (3 ≤ r ∨
        1 ≤ CFSG.pRank 2
          ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N)) ∨
        (3 ≤ CFSG.pRank 2 ↥(K ⟨0, by omega⟩) ∧ 3 ≤ CFSG.pRank 2 ↥(K ⟨1, h⟩) ∧
          (HasStronglyEmbedded ↥(K ⟨0, by omega⟩) ∨ HasStronglyEmbedded ↥(K ⟨1, h⟩) →
            IsTwoDisconnected ↥(K ⟨0, by omega⟩) ∧ IsTwoDisconnected ↥(K ⟨1, h⟩))))

@[expose] def SolomonThm13Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), IsKBalanced N →
    solomonKStarOf N ≤ solomonKStarOf (⊤ : Subgroup G)

end CFSG.ComponentClassification.FooteLit
