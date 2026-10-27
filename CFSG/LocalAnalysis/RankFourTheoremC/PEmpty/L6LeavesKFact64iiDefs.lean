module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup

@[expose] def KFact64iiOuterSylow : Prop :=
  ∀ (p : ℕ), p.Prime → 3 ≤ p → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → CFSG.Open.IsCatalogGroup K →
    CFSG.Open.pRank p (⊤ : Subgroup K) = 1 →
    ∀ φ : MulAut K, orderOf φ = p → φ ∉ (MulAut.conj : K →* MulAut K).range →
      ∀ P : Sylow p K, ∃ g ∈ (P : Subgroup K), φ g ≠ g

@[expose] def KFact64iiI121 : Prop :=
  ∀ (p : ℕ), p.Prime → 3 ≤ p → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → CFSG.Open.IsCatalogGroup K →
    ∀ P : Sylow p K, IsMulCommutative (P : Subgroup K) →
      2 ≤ CFSG.Open.pRank p (P : Subgroup K) →
      ∀ A : Subgroup K, A ≤ (P : Subgroup K) → Nat.card A = p →
        ¬ normalizer ((P : Subgroup K) : Set K) ≤ normalizer (A : Set K)

@[expose] def KFact64iiOuterNPC : Prop :=
  ∀ (p : ℕ), p.Prime → 3 ≤ p → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → CFSG.Open.IsCatalogGroup K →
    CFSG.Open.pRank p (⊤ : Subgroup K) = 1 →
    ∀ φ : MulAut K, orderOf φ = p → φ ∉ (MulAut.conj : K →* MulAut K).range →
      ¬ CFSG.HasNormalPComplement p ↥(Subgroup.closure {g : K | φ g = g})

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
