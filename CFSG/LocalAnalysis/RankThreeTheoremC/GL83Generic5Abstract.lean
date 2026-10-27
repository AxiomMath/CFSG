module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.K1NoBMDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactSections3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.AGLEmbedding
open scoped MatrixGroups

@[expose] def GL83Generic5CaseI : Prop :=
  StronglyEmbeddedRankTwoKFactNoBM → KFactCatalogSchreier → KFactSignalizerTrivial →
  ∀ {p : ℕ} [Fact p.Prime], 5 ≤ p → ∀ {Y : Type} [Group Y] [Finite Y],
    primeComplementCore (G := Y) p = ⊥ → CatalogSimpleSections Y → NoExcludedSection3 Y →
    ∀ {L U Γ : Subgroup Y}, L ≃* PSL(2, GaloisField p 2) → IsSylowOf p U L →
      IsSylowOf p U ⊤ → Γ ≠ ⊤ →
      (∀ D : Subgroup Y, D ≤ U → D ≠ ⊥ → normalizer (D : Set Y) ≤ Γ) → ¬ L ≤ Γ →
      ∀ {W : Subgroup Y}, Nat.Coprime p (Nat.card W) → U ≤ normalizer (W : Set Y) → W = ⊥

@[expose] def GL83Generic5CaseII : Prop :=
  KFactCatalogSchreier → KFactWeakClosure → KFactInnerAction →
  ∀ {p : ℕ} [Fact p.Prime], 5 ≤ p → ∀ {Y : Type} [Group Y] [Finite Y],
    primeComplementCore (G := Y) p = ⊥ → CatalogSimpleSections Y →
    ∀ {L U : Subgroup Y}, L ≃* PSL(2, GaloisField p 2) → IsSylowOf p U L →
      CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3 →
      (∀ Q : Sylow p Y, IsMulCommutative (Q : Subgroup Y)) →
      ∀ {x : Y}, x ≠ 1 → x ^ p = 1 → x ∈ centralizer (L : Set Y) →
      centralizer ({x} : Set Y) ≤ normalizer (L : Set Y) →
      (∀ J : Subgroup Y, J ≤ centralizer ({x} : Set Y) → ⁅J, J⁆ = J → J ≤ L) →
      (∀ Q : Sylow p Y, x ∈ (Q : Subgroup Y) → ∀ g : Y,
        (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup Y) →
          (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x) →
      ∀ {W : Subgroup Y}, Nat.Coprime p (Nat.card W) → U ≤ normalizer (W : Set Y) →
        W ≤ centralizer (L : Set Y)

end CFSG.LocalAnalysis.RankThreeTheoremC
