module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.Assembly.LowTwoRank (StatedSL StatedProj)

variable {H : Type} [Group H]

abbrev OddBar (X : Subgroup H) : Type := ↥X ⧸ pPrimeCore 2 ↥X

abbrev ZStarBar (X : Subgroup H) : Type := ↥X ⧸ Open.fusionZStar ↥X

@[expose] def IsOuterDiagonalPSL2 {Y : Type} [Group Y] (φ : Y ≃* Y) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (e : Y ≃* StatedProj (StatedSL 2 F))
      (A : GL (Fin 2) F), ∀ M N : StatedSL 2 F, (N : GL (Fin 2) F) = A * M * A⁻¹ →
        e (φ (e.symm (QuotientGroup.mk M))) = QuotientGroup.mk N) ∧
    ¬ ∃ g : Y, ∀ y : Y, φ y = g⁻¹ * y * g

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

@[expose] def Table54 : Prop :=
  (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧ Nonempty (OddBar h.J ≃* alternatingGroup (Fin n)) ∧
      ((conjugate h.K h.a = h.K ∧ (Nonempty (OddBar h.K ≃* alternatingGroup (Fin (n + 2))) ∨
          Nonempty (OddBar h.K ≃* alternatingGroup (Fin (n + 4))))) ∨
        (conjugate h.K h.a ≠ h.K ∧ Nat.card (center (OddBar h.K)) = 2 ∧
          Nonempty (ZStarBar h.K ≃* alternatingGroup (Fin n))))) ∨
  ((Blueprint.LieModel (OddBar h.J) .PSL 2 5 1 ∨ Blueprint.LieModel (OddBar h.J) .PSL 2 7 1) ∧
      conjugate h.K h.a = h.K ∧ center (OddBar h.K) ≠ ⊥ ∧
      Blueprint.LieModel (ZStarBar h.K) .PSL 3 2 2) ∨
  (Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2 ∧ conjugate h.K h.a = h.K ∧
      center (OddBar h.K) ≠ ⊥ ∧ Nonempty (ZStarBar h.K ≃* Blueprint.NativeSporadic.Suz)) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f) ∧
      conjugate h.K h.a = h.K ∧ (Blueprint.LieModel (ZStarBar h.K) .PSL 4 p f ∨
        Blueprint.LieModel (ZStarBar h.K) .PSU 4 p f ∨
        ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel (ZStarBar h.K) .POmegaMinus 4 p e)) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      Blueprint.LieModel (OddBar h.J) .PSL 2 p f ∧ conjugate h.K h.a = h.K ∧
      Blueprint.LieModel (OddBar h.K) .PSL 2 p (2 * f)) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      Blueprint.LieModel (OddBar h.J) .PSL 2 p f ∧ conjugate h.K h.a ≠ h.K ∧
      Nat.card (center (OddBar h.K)) = 2 ∧ Blueprint.LieModel (ZStarBar h.K) .PSL 2 p f) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f) ∧
      conjugate h.K h.a = h.K ∧ Blueprint.LieModel (OddBar h.K) .PSp 2 p f)

@[expose] def Table517 : Prop :=
  (conjugate h.K h.a ≠ h.K ∧ Nat.card (center (OddBar h.K)) = 2 ∧
      ((∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧
          Nonempty (OddBar h.J ≃* alternatingGroup (Fin n)) ∧
          Nonempty (ZStarBar h.K ≃* alternatingGroup (Fin n))) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (OddBar h.J) .PSL 2 p f ∧
          Blueprint.LieModel (ZStarBar h.K) .PSL 2 p f)) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      Blueprint.LieModel (OddBar h.J) .PSL 2 p f ∧ conjugate h.K h.a = h.K ∧
      Blueprint.LieModel (OddBar h.K) .PSL 2 p (2 * f)) ∨
  (Nonempty (OddBar h.J ≃* alternatingGroup (Fin 6)) ∧ conjugate h.K h.a = h.K ∧
      Nonempty (OddBar h.K ≃* alternatingGroup (Fin 8))) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f) ∧
      conjugate h.K h.a = h.K ∧ Blueprint.LieModel (OddBar h.K) .PSp 2 p f)

end Hyp52

end CFSG.ComponentClassification.GSThmB
