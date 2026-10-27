module

public import CFSG.GH74.Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFamily
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def Harris36SimpleInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup Y], (∃ a b : Y, a * b ≠ b * a) →
    ∀ p m : ℕ, p.Prime → p ≠ 2 → 1 ≤ m → 16 ∣ p ^ (2 * m) - 1 → IsOfType (HarrisF p) Y →
    (∀ k : ℕ, 1 ≤ k → ¬ Blueprint.LieModel Y .PSL 4 p k ∧ ¬ Blueprint.LieModel Y .PSU 4 p k) →
    ∀ τ : MulAut Y, orderOf τ = 2 →
      Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m →
      (GH74.SectionalTwoRankLE ↥(fixedPoints τ) 3 → τ ∉ innAut Y) ∧
      (τ ∉ innAut Y → GH74.SectionalTwoRankLE ↥(fixedPoints τ) 2 →
        Nonempty (Y ≃* Blueprint.NativeSporadic.J2) ∨
          Nonempty (Y ≃* Blueprint.NativeSporadic.J3) ∨
          Blueprint.LieModel Y .PSL 3 2 2 ∨ Blueprint.LieModel Y .PSL 3 p m ∨
          Blueprint.LieModel Y .PSU 3 p m ∨ Blueprint.LieModel Y .PSL 2 p (2 * m))

@[expose] def IsMType (p : ℕ) (H : Type) [Group H] : Prop :=
  IsTwoQuasisimple H ∧
    (∃ (tag : Assembly.LowTwoRank.StatedLieTag) (n k : ℕ),
      Blueprint.LieModel (H ⧸ Open.fusionZStar H) tag n p k) ∧
    Even (Nat.card (Open.fusionZStar H)) ∧
    ∀ n k : ℕ,
      (Blueprint.LieModel (H ⧸ Open.fusionZStar H) .PSL (2 * n) p k →
        (Nat.card (Open.fusionZStar H)).factorization 2 =
          (Nat.gcd (2 * n) (p ^ k - 1)).factorization 2) ∧
      (Blueprint.LieModel (H ⧸ Open.fusionZStar H) .PSU (2 * n) p k →
        (Nat.card (Open.fusionZStar H)).factorization 2 =
          (Nat.gcd (2 * n) (p ^ k + 1)).factorization 2)

@[expose] def Harris36NonsimpleInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → ¬ IsSimpleGroup Y →
    IsPGroup 2 ↥(center Y) →
    ∀ p m : ℕ, p.Prime → p ≠ 2 → 1 ≤ m → 16 ∣ p ^ (2 * m) - 1 → IsOfType (HarrisF p) Y →
    ¬ IsMType p Y →
    ∀ τ : MulAut Y, orderOf τ = 2 →
      Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m →
      (Nonempty (Y ⧸ center Y ≃* Blueprint.NativeSporadic.J2) ∧ Nat.card ↥(center Y) = 2 ∧
          τ ∉ innAut Y) ∨
        (Nonempty (Y ⧸ center Y ≃* Blueprint.NativeSporadic.HS) ∧ Nat.card ↥(center Y) = 2 ∧
          τ ∈ innAut Y ∧ ∀ e : Y, MulAut.conj e = τ → e ^ 2 ≠ 1) ∨
        (Blueprint.LieModel (Y ⧸ center Y) .PSL 3 2 2 ∧ Nat.card ↥(center Y) < 16 ∧
          τ ∉ innAut Y) ∨
        ∃ k : ℕ, 1 ≤ k ∧ (Blueprint.LieModel (Y ⧸ center Y) .PSL 4 p k ∨
          Blueprint.LieModel (Y ⧸ center Y) .PSU 4 p k)

end CFSG.ComponentClassification.HarrisLit
