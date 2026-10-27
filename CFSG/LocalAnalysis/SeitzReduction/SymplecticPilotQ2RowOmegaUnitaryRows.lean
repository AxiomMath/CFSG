module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Rows

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def SpTwoRowEightInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → n = 3 →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k κ) → False

theorem spTwoRowInput_of_eight_of_four_le {κ : Sp2mKind} (h8 : SpTwoRowEightInput κ)
    (hhigh : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
      ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (n + 1), NsKindSp e t k κ) → False) :
    SpTwoRowInput κ := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot
  rcases (show n = 3 ∨ 4 ≤ n by omega) with h3 | h4
  · exact h8 G L hset n K hK h3 e t ht hKt hroot
  · exact hhigh G L hset n K hK h4 e t ht hKt hroot

end CFSG.SeitzReduction.SymplecticPilot
