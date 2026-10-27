module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)

@[expose] def KFactL28Three : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeL28 K → ∀ (T : Sylow 3 K),
    Nat.card (T : Subgroup K) = 3 ^ 2 ∧
    ∀ Y : Subgroup K, normalizer ((T : Subgroup K) : Set K) ≤ Y →
      Y = normalizer ((T : Subgroup K) : Set K) ∨ Y = ⊤

@[expose] def KFactL28BorelCore : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    centralizer (K : Set X) = ⊥ → IsRankThreeL28 ↥K →
    ∀ T : Subgroup X, T ≤ K → IsSylowOf 3 T K →
      rankThreePrimeCore 3 (normalizer (T : Set X)) = ⊥

@[expose] def KFactL28FieldSignalizer : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeL28 K → ∀ (T : Sylow 3 K) (α : MulAut K),
    orderOf α = 3 → (∀ k : K, α ≠ MulAut.conj k) → (T : Subgroup K).map α.toMonoidHom = T →
      ⊤ ≤ rankThreeGamma 1 3 (T : Subgroup K) ⊔
        sSup {V : Subgroup K | IsPGroup 2 V ∧ V.map α.toMonoidHom = V}

end CFSG.LocalAnalysis.RankThreeTheoremC
