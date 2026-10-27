module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut IsLocallyBalanced IsWeaklyLocallyBalanced)
open scoped MatrixGroups

namespace Sec13e

@[expose] def Input22_3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime →
    ∀ (L B K₁ : Subgroup X) (𝒦 : Set (Subgroup X)), K₁ ∈ 𝒦 →
      (∀ K ∈ 𝒦, IsComponentOf K L) → L = ⨆ K ∈ 𝒦, K →
      (∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K ≠ K' → ⁅K, K'⁆ = ⊥) →
      (∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, ∃ b ∈ B, GLBConj b K = K') →
      IsElemAbelian p B → B ≤ Subgroup.normalizer (L : Set X) → p ∣ Nat.card ↥L →
      (∀ b ∈ {b : X | b ∈ B ∧ b ≠ 1 ∧
          (b ∈ Subgroup.centralizer (L : Set X) ∨ b ∉ Subgroup.normalizer (K₁ : Set X))},
        ∀ Y : Subgroup X, IsComponentOf Y (GLAPLayer p (L ⊓ Subgroup.centralizer ({b} : Set X))) →
          ∃ K ∈ 𝒦, ∃ φ : ↥K →* ↥Y, Function.Surjective φ ∧ φ.ker ≤ Subgroup.center ↥K) ∧
      ((∃ b : X, b ∈ B ∧ b ≠ 1 ∧
          (b ∈ Subgroup.centralizer (L : Set X) ∨ b ∉ Subgroup.normalizer (K₁ : Set X))) →
        p ^ 2 ≤ Nat.card ↥B →
        L = ⨆ (b : X) (_ : b ∈ B ∧ b ≠ 1 ∧
            (b ∈ Subgroup.centralizer (L : Set X) ∨ b ∉ Subgroup.normalizer (K₁ : Set X))),
          GLAPLayer p (L ⊓ Subgroup.centralizer ({b} : Set X)))

@[expose] def Input7_1Aut : Prop :=
  ∀ (p : ℕ), p.Prime → 3 ≤ p → ∀ (K : Type) [Group K] [Finite K],
    CFSG.Open.IsQuasisimple K → Subgroup.center K = ⊥ →
    (IsAltType (p + 2) K ∨ (3 < p ∧ ∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) K ∧
        HasFixedPointFreeOrder ε n p ∧ CFSG.Open.pRank p (⊤ : Subgroup K) = 1)) →
    ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card ↥E ≤ p

theorem commute_of_isComponentOf {X : Type} [Group X] [Finite X] {K K' : Subgroup X}
    (hK : IsComponentOf K ⊤) (hK' : IsComponentOf K' ⊤) (hne : K ≠ K') : ⁅K, K'⁆ = ⊥ := by
  rcases CFSG.LocalCores.distinct_components_commute ((CFSG.isComponent_iff_open K).2 hK)
      ((CFSG.isComponent_iff_open K').2 hK') with h | h
  · exact absurd h hne
  · exact h

end Sec13e

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
