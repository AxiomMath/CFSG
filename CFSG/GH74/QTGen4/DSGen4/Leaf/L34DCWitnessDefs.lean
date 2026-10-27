module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCWitnessA

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def WitnessLn (F : Type) [Field F] [Finite F] [CharP F 2] (κ : F) : Prop :=
  ∃ a : MulAut ↥(Ln F),
    (∀ m : ↥(Ln F), (m : projectiveSL 3 F) ∈ Pt F ↔
      ((a m : ↥(Ln F)) : projectiveSL 3 F) ∈ Pt F) ∧
    ∀ (b : ↥(Ln F ⊓ Pt F)) (m : ↥(Ln F)), (m : projectiveSL 3 F) = (b : projectiveSL 3 F) →
      ((a m : ↥(Ln F)) : projectiveSL 3 F) =
        ((nuMap 1 1 κ 0 false b : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F)

@[expose] def WitnessPt (F : Type) [Field F] [Finite F] [CharP F 2] (κ : F) : Prop :=
  ∃ a : MulAut ↥(Pt F),
    (∀ m : ↥(Pt F), (m : projectiveSL 3 F) ∈ Ln F ↔
      ((a m : ↥(Pt F)) : projectiveSL 3 F) ∈ Ln F) ∧
    ∀ (b : ↥(Ln F ⊓ Pt F)) (m : ↥(Pt F)), (m : projectiveSL 3 F) = (b : projectiveSL 3 F) →
      ((a m : ↥(Pt F)) : projectiveSL 3 F) =
        ((nuMap 1 1 0 κ false b : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F)

end CFSG.GH74.QTGen4.DSGen4.L34
