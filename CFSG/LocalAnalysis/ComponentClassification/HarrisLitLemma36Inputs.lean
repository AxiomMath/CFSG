module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTheorem1

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup
open scoped MatrixGroups

@[expose] def Harris81Lemma36NonsimpleInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsQuasisimple G → pPrimeCore 2 G = ⊥ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → IsOfType (InClosure (IsSimpleChevalleyOver p)) G →
    ∀ τ : MulAut G, orderOf τ = 2 →
    ∀ m : ℕ, 1 ≤ m → 16 ∣ p ^ (2 * m) - 1 →
    ∀ K : Subgroup G, IsTwoComponentIn K (fixedPoints τ) →
      (∀ K' : Subgroup G, IsTwoComponentIn K' (fixedPoints τ) → K' = K) →
      Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSL 2 p m →
      ¬ IsSimpleGroup G → ¬ IsMType p G →
      (Nonempty (G ⧸ center G ≃* Blueprint.NativeSporadic.J2) ∧ Nat.card ↥(center G) = 2 ∧
          τ ∉ innAut G) ∨
        (Nonempty (G ⧸ center G ≃* Blueprint.NativeSporadic.HS) ∧ Nat.card ↥(center G) = 2 ∧
          Nonempty (↥(generalizedFitting ↥(fixedPoints τ)) ≃*
            Multiplicative (ZMod 4) × ↥(alternatingGroup (Fin 6))) ∧
          τ ∈ innAut G) ∨
        (Blueprint.LieModel (G ⧸ center G) .PSL 3 2 2 ∧ Nat.card ↥(center G) < 16 ∧
          τ ∉ innAut G) ∨
        (∃ k : ℕ, m = 2 * k ∧
          (Blueprint.LieModel (G ⧸ center G) .PSL 4 p k ∨
            Blueprint.LieModel (G ⧸ center G) .PSU 4 p k))

@[expose] def TwoJ2OuterInvolutionIndexFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y →
    Nonempty (Y ⧸ center Y ≃* Blueprint.NativeSporadic.J2) → Nat.card ↥(center Y) = 2 →
    ∀ τ : MulAut Y, orderOf τ = 2 → τ ∉ innAut Y →
      4 * twoPart (fixedPoints τ) ≤ twoPart (⊤ : Subgroup Y)

@[expose] def TwoHSInnerInvolutionIndexFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y →
    Nonempty (Y ⧸ center Y ≃* Blueprint.NativeSporadic.HS) → Nat.card ↥(center Y) = 2 →
    ∀ τ : MulAut Y, orderOf τ = 2 → τ ∈ innAut Y →
      Nonempty (↥(generalizedFitting ↥(fixedPoints τ)) ≃*
        Multiplicative (ZMod 4) × ↥(alternatingGroup (Fin 6))) →
      4 * twoPart (fixedPoints τ) ≤ twoPart (⊤ : Subgroup Y)

end CFSG.ComponentClassification.HarrisLit
