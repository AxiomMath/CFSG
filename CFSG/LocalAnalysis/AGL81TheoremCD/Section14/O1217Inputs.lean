module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.S15

@[expose] def NineFourTwoSigmaGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
    AGL81C.NineSettingGen G M p Q H E 2 → p ∈ sigmaM G M → ¬ AGL81C.pLayerIn p H ≤ M →
      (∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M) → rankThreeGamma 1 p P ≤ M) →
        ((AGL81C.kSub p M H).subgroupOf H).Normal ∧ AGL81C.xSub p M H ≤ M ∧
          Nat.Coprime p (Nat.card (AGL81C.xSub p M H)) ∧
          CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup p ↥(AGL81C.kStar p M H)

@[expose] def KFactL34InvTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    CFSG.AGLEmbedding.IsLinThreeFour ↥K →
    ∀ T : Sylow 3 ↥K, ∀ S : Subgroup X, IsPGroup 2 S →
      (T : Subgroup ↥K).map K.subtype ≤ Subgroup.normalizer (S : Set X) →
      (Subgroup.centralizer (K : Set X)).relIndex S ≤ 2

@[expose] def KFactThreeEightFive : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q ↥K →
    2 ≤ CFSG.Open.pRank q (⊤ : Subgroup X) →
    ∀ X₁ : Subgroup X, CFSG.RankThree.PartOne.IsStronglyPEmbedded q X₁ →
    ∀ D : Subgroup X, (∃ d : ℕ, d.Prime ∧ d ≠ 2 ∧ d ≠ q ∧ Nat.card D = d) →
      q ∣ Nat.card ↥(X₁ ⊓ Subgroup.centralizer (D : Set X)) →
      ¬ (K ⊓ Subgroup.centralizer (D : Set X) ≤ X₁)

@[expose] def KFactCentralLift : Prop :=
  ∀ q p : ℕ, q.Prime → q ≠ 2 → p.Prime → p ≠ 2 → p ≠ q →
    ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), CFSG.IsQuasisimple ↥K →
      CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q (↥K ⧸ Subgroup.center ↥K) →
      Odd (Nat.card (Subgroup.center ↥K)) → ¬ q ∣ Nat.card (Subgroup.center ↥K) →
      p ∣ Nat.card (Subgroup.center ↥K) →
      ∀ b : X, b ∈ Subgroup.normalizer (K : Set X) → orderOf b = p →
        b ∉ Subgroup.centralizer (K : Set X) →
      ∀ K₁ : Subgroup X, K₁ < K → (Subgroup.center ↥K).map K.subtype ≤ K₁ →
        (∃ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf q S K ∧
          K ⊓ Subgroup.normalizer (S : Set X) ≤ K₁) →
        ¬ (K ⊓ Subgroup.centralizer ({b} : Set X) ≤ K₁)

@[expose] def KFactAltSixCoreCentral : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Group.IsPerfect K → ∀ N : Subgroup K, (hN : N.Normal) →
    IsSolvable ↥N → Nat.Coprime (Nat.card N) 6 →
    Nonempty (K ⧸ N ≃* alternatingGroup (Fin 6)) →
    (∀ r : ℕ, r.Prime → CFSG.Open.pRank r N ≤ 3) → N ≤ Subgroup.center K

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
