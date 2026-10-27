module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenSolvDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LargeField

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def SolvSigmaSylowFacts (K : Type) [Group K] : Prop :=
  ∀ S : Sylow 3 K, ∃ A : Subgroup K, A ≤ S ∧ IsElemAbelian 3 A ∧ Nat.card A = 27 ∧
    (∀ r ∈ (S : Subgroup K), r ∉ A →
      ∃ g ∈ normalizer (A : Set K), g * r * g⁻¹ ∉ (S : Subgroup K)) ∧
    (∀ a ∈ A, a ≠ 1 → ∃ g₁ ∈ normalizer (A : Set K), ∃ g₂ ∈ normalizer (A : Set K),
      g₁ * a * g₁⁻¹ ∉ zpowers a ∧ g₂ * a * g₂⁻¹ ∉ zpowers a ∧
        g₂ * a * g₂⁻¹ ∉ zpowers (g₁ * a * g₁⁻¹))

@[expose] def KFactParabolicSymThreeNormal : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup A), Open.IsQuasisimple ↥Y →
    pCoreOf 2 Y = ⊥ → IsClassicalTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y) → IsParabolicTwo Y P →
    ∀ T ∈ cZero P, Nonempty (↥T ⧸ CFSG.pCore 2 ↥T ≃* Equiv.Perm (Fin 3)) →
      P ≤ normalizer (T : Set A) ∧
        ∀ d : TauCeti.ValidLieTypeIndex, IsClassicalOrG2Index d.1 →
          Nonempty (↥Y ⧸ Subgroup.center ↥Y ≃* (TauCeti.CFSGIndex.lie d).Group) →
            CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LieField d.1 = 2

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81TenTwelveSolvSigma : Prop :=
  Setting G → 3 ∈ rankThreeSigmaA G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    AGL81CfgData 3 P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ I₀ ∈ cZero (H ⊓ L), IsSymThreeOrSUThreeTwo (↥I₀ ⧸ CFSG.pCore 2 ↥I₀) →
    (IsLieOver K (.twistedA 3) 2 1 ∨ IsLieOver K (.B 3) 2 1 ∨
      Nonempty (K ≃* alternatingGroup (Fin 9))) →
    ∀ J : Subgroup (H ⧸ primeComplementCore (G := H) 3),
      J = ((CFSG.ComponentClassification.AS76b.oUpperTwo I₀).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) 3)) →
      J ≤ K → IsPGroup 3 J → IsSubnormal J (K ⊓ d1X0 3 M H) →
      SolvThreeDirectCond (d1X0 3 M H) J → J = ⊥

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
