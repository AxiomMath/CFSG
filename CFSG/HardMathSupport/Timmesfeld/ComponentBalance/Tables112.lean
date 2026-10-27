module

public import CFSG.LocalAnalysis.GLTheoremB.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def IsInnerAut {L : Type*} [Group L] (ψ : MulAut L) : Prop :=
  ∃ g : L, ∀ t, ψ t = g * t * g⁻¹

@[expose] def FieldBonus (L : Type) [Group L] [Finite L] (p : ℕ) (H : Subgroup (MulAut L)) : Prop :=
  ∃ ψ ∈ H, ¬ IsInnerAut ψ ∧
    ∃ T : Subgroup L, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T.map ψ.toMonoidHom = T ∧
    ∃ E₁ E₂ : Subgroup L, IsElemAbelian p E₁ ∧ IsElemAbelian p E₂ ∧
      E₁ ≤ Subgroup.normalizer (T : Set L) ∧
      Nat.card E₁ = p ^ GLATwoLocalRank p L ∧ Nat.card E₂ = p ^ pRank p (⊤ : Subgroup L) ∧
      (∀ e ∈ E₁, ψ e = e) ∧ (∀ e ∈ E₂, ψ e = e)

structure Tables112 : Prop where
  T0 : ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∃ t : L, orderOf t = 2
  T1a : ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      pRank p (⊤ : Subgroup (MulAut L)) ≤ pRank p (⊤ : Subgroup L) + 2
  T1b : ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      (pRank p (⊤ : Subgroup L) < 7 ∨ p ∣ Nat.card (Subgroup.center L)) →
      pRank p (⊤ : Subgroup (MulAut L)) ≤ pRank p (⊤ : Subgroup L) + 1
  T2 : ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      2 * pRank p (Subgroup.center L) ≤ pRank p (⊤ : Subgroup L)
  T3 : ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∀ p : ℕ, p.Prime → p ≠ 2 → IsPGroup p (Subgroup.center L) →
      pRank p (Subgroup.center L) = 1 →
      (p = 3 ∧ Nat.card (Subgroup.center L) = 3) ∨
        p + 2 ≤ (p - 2) * pRank p (⊤ : Subgroup L)
  T11 : ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∀ p : ℕ, p.Prime → p ≠ 2 → IsPGroup p (Subgroup.center L) →
      2 ≤ pRank p (Subgroup.center L) →
      p = 3 ∧ pRank 3 (Subgroup.center L) = 2 ∧ pRank 3 (⊤ : Subgroup L) = 6 ∧
        pRank 3 (⊤ : Subgroup (MulAut L)) ≤ 6
  T9 : ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → CFSG.Open.IsKGroup L →
    Nat.card (Subgroup.center L) = 1 → pRank 3 (⊤ : Subgroup L) = 2 →
      GLATwoLocalRank 3 L = 0 → pRank 3 (⊤ : Subgroup (MulAut L)) ≤ 2
  TFA_a : ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → CFSG.Open.IsKGroup L →
    Nat.card (Subgroup.center L) = 1 → pRank 3 (⊤ : Subgroup L) = 1 →
      GLATwoLocalRank 3 L = 1 → ∀ H : Subgroup (MulAut L), IsElemAbelian 3 H →
        Nat.card H = 9 → FieldBonus L 3 H
  TFA_b : ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → CFSG.Open.IsKGroup L →
    Nat.card (Subgroup.center L) = 3 → pRank 3 (⊤ : Subgroup L) = 2 →
      GLATwoLocalRank 3 L = 1 → ∀ H : Subgroup (MulAut L), IsElemAbelian 3 H →
        Nat.card H = 27 → FieldBonus L 3 H

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
