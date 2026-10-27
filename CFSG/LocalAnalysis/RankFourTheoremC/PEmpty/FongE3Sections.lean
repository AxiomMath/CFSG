module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongE3Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.Blueprint Subgroup

@[expose] def NoMonsterQuasisimple (Z : Type) [Group Z] : Prop :=
  ∀ K : Subgroup Z, Open.IsQuasisimple ↥K → ¬ P64IsSpor .M (↥K ⧸ center ↥K)

@[expose] def NoMonsterSection (A : Type) [Group A] : Prop :=
  ∀ (H : Subgroup A) (N : Subgroup ↥H) [N.Normal], NoMonsterQuasisimple (↥H ⧸ N)

@[expose] def KFactP65RankTwoE3 : Prop :=
  ∀ (A : Type) [Group A] [Finite A], NoMonsterSection A → KFactP65RankTwoAt A

@[expose] def KDI278SporCNoM : Prop :=
  ∀ (p : ℕ) (s : TauCeti.SporadicName), P64SporPairC p s → s ≠ .M → ∀ (Z : Type) [Group Z]
    [Finite Z] (K : Subgroup Z), K.Normal → P64IsSpor s ↥K → centralizer (K : Set Z) = ⊥ →
      ∀ B : Subgroup Z, IsElemAbelian p B → Nat.card B = p ^ 2 →
        (∀ y ∈ centralizer (B : Set Z), y ^ p = 1 → y ∈ B) →
          ∀ W : Subgroup Z, B ≤ normalizer (W : Set Z) → Nat.Coprime (Nat.card W) (2 * p) →
            W = ⊥

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
