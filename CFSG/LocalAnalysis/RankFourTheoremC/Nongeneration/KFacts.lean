module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallIdent
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding

@[expose] def GL83I241 : Prop := KFactSmallIdent ∧ KFactOneLieIdent

@[expose] def GL83I2316 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ 2 →
        ¬ E ≤ (MulAut.conj : K →* MulAut K).range →
        Subgroup.closure {k : K | ∃ e ∈ E, e ≠ 1 ∧ e k = k} = ⊤

end CFSG.LocalAnalysis.RankFourTheoremC
