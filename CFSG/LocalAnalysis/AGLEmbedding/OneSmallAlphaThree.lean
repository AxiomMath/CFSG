module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin

@[expose] def KFactAlphaThreeWeak : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
    IsCatalogGroup (K ⧸ Subgroup.center K) →
    Subgroup.center K ≠ ⊥ → IsPGroup 3 (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    KOutTwoGroup K → ∀ T : Sylow 3 K,
      ((∃ A : Subgroup K, A ≤ (T : Subgroup K) ⊓ Subgroup.centralizer (T : Set K) ∧
            IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2) ∨
          (∃ A : Subgroup K, A ≤ (T : Subgroup K) ∧
            (T : Subgroup K) ≤ Subgroup.normalizer (A : Set K) ∧ IsElemAbelian 3 A ∧
            3 ^ (3 + 1) ≤ Nat.card A)) →
      (GLBWeakCore 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank 3 (⊤ : Subgroup K)) ∨
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)

@[expose] def KFactJ3Involve : Prop :=
  ∀ (KC : Type) [Group KC] [Finite KC],
    Nonempty (KC ⧸ Subgroup.center KC ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) →
    ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
      IsCatalogGroup L → ∀ TL : Sylow 3 L, ¬ IsCyclic (TL : Subgroup L) →
      GLBCore 3 1 (TL : Subgroup L) ≠ ⊤ → Open.pRank 3 (⊤ : Subgroup (MulAut L)) ≤ 2 →
    ∀ (A : Subgroup KC) (f : A →* L), Function.Surjective f → IsAltTwoP 3 L

end CFSG.AGLEmbedding
