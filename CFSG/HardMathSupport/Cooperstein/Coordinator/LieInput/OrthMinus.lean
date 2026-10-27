module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Quotient

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted

@[expose] def OrthMinusLeviOb : Prop :=
  ∀ (n f : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (_hadm : StatedLieAdmissible .POmegaMinus n 2 f),
    Nat.card F = 2 ^ f → ∀ {Y : Type} [Group Y] (π : spinGroup (quadMinus n F b c) →* Y),
      (∀ z ∈ π.ker, z ∈ Subgroup.center (spinGroup (quadMinus n F b c))) →
        ∀ I : Set (Fin (n - 1)), I ≠ Set.univ →
          LeviOb (minusDatum n hirr) (minusTorus n hirr) π I

@[expose] def OrthMinusCentOb : Prop :=
  ∀ (n f : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (_hadm : StatedLieAdmissible .POmegaMinus n 2 f),
    Nat.card F = 2 ^ f → ∀ I : Set (Fin (n - 1)), I ≠ Set.univ →
      CentOb (minusDatum n hirr) I

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

end
