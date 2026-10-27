module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitInputs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def fixedPoints {Y : Type} [Group Y] (k : MulAut Y) : Subgroup Y :=
  MonoidHom.eqLocus k.toMonoidHom (MonoidHom.id Y)

theorem mem_fixedPoints {Y : Type} [Group Y] {k : MulAut Y} {y : Y} :
    y ∈ fixedPoints k ↔ k y = y :=
  Iff.rfl

@[expose] def AutPSL2FieldCentralizerInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → Even f → 16 ∣ p ^ f - 1 →
    Blueprint.LieModel Y .PSL 2 p f → ∀ k : MulAut Y, IsFieldAutPSL2 k →
      Blueprint.LieModel ↥(perfectResidual ↥(fixedPoints k)) .PSL 2 p (f / 2) ∧
      2 * Nat.card (perfectResidual ↥(fixedPoints k)) = Nat.card (fixedPoints k) ∧
      (Nat.card (fixedPoints k)).factorization 2 = (Nat.card Y).factorization 2 ∧
      ∀ φ : MulAut Y,
        (∀ y ∈ (perfectResidual ↥(fixedPoints k)).map (fixedPoints k).subtype, φ y = y) →
          φ = 1 ∨ φ = k

end CFSG.ComponentClassification.HarrisLit
