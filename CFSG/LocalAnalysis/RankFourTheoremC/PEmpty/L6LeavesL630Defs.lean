module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open CFSG.Open Subgroup

@[expose] def IsInvolvedIn (H K : Type) [Group H] [Group K] : Prop :=
  ∃ (A : Subgroup K) (N : Subgroup A) (_ : N.Normal), Nonempty ((A ⧸ N) ≃* H)

@[expose] def KFactI2026 : Prop :=
  ∀ (q : ℕ) (E : Type) [Group E] [Finite E], q.Prime → q ≠ 2 →
    (∀ a b : E, a * b = b * a) → (∀ e : E, e ^ q = 1) → Nat.card E = q ^ 4 →
    ∀ (X P S : Subgroup (MulAut E)), P ≤ X → Nat.card P = 5 → S ≤ X → S ≤ pCoreOf 2 X →
      ⁅S, P⁆ = S → CFSG.LocalAnalysis.RankThreeTheoremC.smallRankIsQ8D8 S →
      (∀ g ∈ rankThreePrimeCore 2 X, ∃ k : ℕ, ∀ e : E, g e = e ^ k) ∧
      (∀ _ : ((rankThreePrimeCore 2 X ⊔ pCoreOf 2 X).subgroupOf X).Normal,
        IsInvolvedIn (↥X ⧸ (rankThreePrimeCore 2 X ⊔ pCoreOf 2 X).subgroupOf X)
          (Equiv.Perm (Fin 6)))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
