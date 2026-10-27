module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15

@[expose] def NineSevenOneGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
    NineSettingGen G M p Q H E 2 → H ∈ H2Fam M Q → p ∉ sigmaM G M → 5 ≤ p →
    pCoreOf 2 (H ⊓ M) = pCoreOf 2 H

@[expose] def NineSevenOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
    NineSetting G M p Q H E 2 → H ∈ H2Fam M Q → p ∉ sigmaM G M → 5 ≤ p →
    pCoreOf 2 (H ⊓ M) = pCoreOf 2 H

@[expose] def NineSevenOneAt (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  ∀ (Q H E : Subgroup G) (p : ℕ), NineSettingGen G M p Q H E 2 → H ∈ H2Fam M Q →
    p ∉ sigmaM G M → 5 ≤ p → pCoreOf 2 (H ⊓ M) = pCoreOf 2 H

theorem NineSevenOneGen.nineSevenOneAt (h : NineSevenOneGen) {G : Type} [Group G] [Finite G]
    {M : Subgroup G} : NineSevenOneAt G M :=
  fun Q H E p hn hH hp h5 => h G M Q H E p hn hH hp h5

theorem NineSevenOne.nineSevenOneAt (h : NineSevenOne) {G : Type} [Group G] [Finite G]
    {M : Subgroup G} (hC : CStarSetting G M) : NineSevenOneAt G M :=
  fun Q H E p hn hH hp h5 => h G M Q H E p (nineSetting_iff_gen.mpr ⟨hC, hn⟩) hH hp h5

@[expose] def KFactThreeSevenTwoGe5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ K E S : Subgroup X, K.Normal → CFSG.IsQuasisimple ↥K →
      CFSG.pPrimeCore p ↥K = ⊥ → IsElemAbelian p E → Nat.card E = p ^ 2 →
      (∀ T : Subgroup X, T ≠ ⊥ → IsPGroup 2 T →
        pRank p (Subgroup.normalizer (T : Set X)) ≤ 3) →
      pRank p (rankThreeGamma 1 p E) ≤ 3 → ¬ K ≤ rankThreeGamma 1 p E →
      IsPGroup 2 S → rankThreeGamma 1 p E ≤ Subgroup.normalizer (S : Set X) →
      ¬ S ≤ Subgroup.centralizer (K : Set X) →
      p = 5 ∧ CFSG.AGLEmbedding.IsFi22 ↥K

@[expose] def KFactFi22ThreeRank : Prop :=
  ∀ (X F : Type) [Group X] [Finite X] [Group F], CFSG.AGLEmbedding.IsFi22 F →
    ∀ φ : X →* F, Function.Surjective φ → 5 ≤ pRank 3 (⊤ : Subgroup X)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
