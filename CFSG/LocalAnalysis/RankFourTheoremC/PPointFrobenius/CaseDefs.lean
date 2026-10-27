module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KC.Statement

public section

open Subgroup
open scoped MatrixGroups commutatorElement

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding

@[expose] def FrobCaseI : Prop :=
  StronglyEmbeddedPSL2KFact → KFactCatalogSchreier →
  ∀ {p n : ℕ} [Fact p.Prime], 5 ≤ p → 3 ≤ n → ∀ {Y : Type} [Group Y] [Finite Y],
    primeComplementCore (G := Y) p = ⊥ → CatalogSimpleSections Y →
    ∀ {L U Γ : Subgroup Y}, L ≃* PSL(2, GaloisField p n) → IsSylowOf p U L →
      IsSylowOf p U ⊤ → Γ ≠ ⊤ →
      (∀ D : Subgroup Y, D ≤ U → D ≠ ⊥ → normalizer (D : Set Y) ≤ Γ) → ¬ L ≤ Γ →
      ∀ {W : Subgroup Y}, Nat.Coprime p (Nat.card W) → U ≤ normalizer (W : Set Y) → W = ⊥

structure FrobCaseIIHyp (p n : ℕ) [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
    (L U : Subgroup Y) (x : Y) : Prop where
  five_le : 5 ≤ p
  three_le : 3 ≤ n
  core_eq_bot : primeComplementCore (G := Y) p = ⊥
  catalog : CatalogSimpleSections Y
  equiv : Nonempty (L ≃* PSL(2, GaloisField p n))
  sylow : IsSylowOf p U L
  pRank_le : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ n + 1
  abelian : ∀ Q : Sylow p Y, IsMulCommutative (Q : Subgroup Y)
  ne_one : x ≠ 1
  pow_eq_one : x ^ p = 1
  mem_centralizer : x ∈ centralizer (L : Set Y)
  centralizer_le : centralizer ({x} : Set Y) ≤ normalizer (L : Set Y)
  perfect_le : ∀ J : Subgroup Y, J ≤ centralizer ({x} : Set Y) → ⁅J, J⁆ = J → J ≤ L
  weakClosed : ∀ Q : Sylow p Y, x ∈ (Q : Subgroup Y) → ∀ g : Y,
    (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup Y) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
