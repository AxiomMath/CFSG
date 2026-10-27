module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def KFactCaseTwoReeId : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ T : Sylow 3 K, ¬ IsCyclic (T : Subgroup K) →
      GLBCore 3 1 (T : Subgroup K) ≠ ⊤ → 3 ≤ Open.pRank 3 (⊤ : Subgroup (MulAut K)) →
      ∀ (A : Subgroup K) (L : Type) [Group L], IsCaseTwoGroup 3 L →
        ∀ f : A →* L, Function.Surjective f →
        ∃ d : TauCeti.ValidLieTypeIndex, IsReeGTwoIndex 3 d ∧
          Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def KFactReeInvolution : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsReeGTwoIndex 3 d →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ U : Sylow 3 L,
    ∃ J ∈ Subgroup.normalizer ((U : Subgroup L) : Set L), orderOf J = 2 ∧
      (∀ t ∈ Subgroup.normalizer ((U : Subgroup L) : Set L), orderOf t = 2 →
        ∃ u ∈ (U : Subgroup L), t = u * J * u⁻¹) ∧
      IsElemAbelian 3 ((U : Subgroup L) ⊓ Subgroup.centralizer ({J} : Set L)) ∧
      Nat.card ((U : Subgroup L) ⊓ Subgroup.centralizer ({J} : Set L) : Subgroup L) =
        3 ^ d.1.fieldExponent ∧
      ¬ Subgroup.centralizer ({J} : Set L) ≤ Subgroup.normalizer ((U : Subgroup L) : Set L)

@[expose] def KFactL28AutThree : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsCaseTwoGroup 3 L →
    ∀ A : Subgroup (MulAut L), IsPGroup 3 A → Nat.card A ≤ 27

end CFSG.AGLEmbedding
