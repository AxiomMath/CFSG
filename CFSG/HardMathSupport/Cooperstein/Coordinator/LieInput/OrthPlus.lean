module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Quotient

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin

@[expose] def OrthPlusLeviOb : Prop :=
  ∀ (n f : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    (_hadm : StatedLieAdmissible .POmegaPlus n 2 f) (hn : 3 ≤ n),
    Nat.card F = 2 ^ f → ∀ {Y : Type} [Group Y] (π : spinGroup (quadPlus n F) →* Y),
      (∀ z ∈ π.ker, z ∈ Subgroup.center (spinGroup (quadPlus n F))) →
        ∀ I : Set (Fin n), I ≠ Set.univ →
          LeviOb (plusDatum n F hn) (fun k => (torusD F hn k).range) π I

@[expose] def OrthPlusCentOb : Prop :=
  ∀ (n f : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    (_hadm : StatedLieAdmissible .POmegaPlus n 2 f) (hn : 3 ≤ n),
    Nat.card F = 2 ^ f → ∀ I : Set (Fin n), I ≠ Set.univ →
      CentOb (plusDatum n F hn) I

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

end
