module

public import CFSG.Open.Defs
public import CFSG.Open.LocalVocabulary
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

@[expose] def IsLinearOrUnitaryAt (p : ℕ) (X : Type) [Group X] : Prop :=
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), p ∣ n ∧ p ∣ Nat.card K - 1 ∧
      Nonempty (X ≃* StatedProj (StatedSL n K))) ∨
    (∃ (n q : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ 2 ∧ p ∣ n ∧
      p ∣ q + 1 ∧ Nonempty (X ≃* StatedProj (StatedSU n q K)))

@[expose] def GL83PElementCentralizerRank : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L →
    IsLinearOrUnitaryAt p (L ⧸ center L) → center L ≠ ⊥ → IsPGroup p (center L) →
      ∀ d : L, d ^ p = 1 → d ∉ center L → 3 ≤ CFSG.Open.pRank p (centralizer ({d} : Set L))

@[expose] def GL83OutDiagPowerMap : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L →
    IsLinearOrUnitaryAt p (L ⧸ center L) → center L ≠ ⊥ → IsPGroup p (center L) →
      ∀ (α δ : MulAut L) (a b : ℕ), δ ^ p = 1 → δ ∉ (MulAut.conj : L →* MulAut L).range →
        α * δ * α⁻¹ = δ ^ b → (∀ c ∈ center L, c ^ p = 1 → α c = c ^ a) →
          (a : ZMod p) = b ∨ (b : ZMod p) = 1

end CFSG.LocalAnalysis.RankFourTheoremC
