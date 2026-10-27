module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf19Thm3A

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ComponentClassification.AS76b

namespace Thm3A

section Rows

variable {Y : Type} [Group Y]

@[expose] def Thm3RowG23 (P : Subgroup Y) : Prop :=
  CFSG.Blueprint.LieModel (SecQuot P) .G2 0 3 1

@[expose] def Thm3RowsG (Ω : Set (Subgroup Y)) (P : Subgroup Y) : Prop :=
  Thm3RowG23 P ∨ Thm3RowsA Ω P

theorem Thm3RowG23.toRowG2 {P : Subgroup Y} (h : Thm3RowG23 P) : Thm3RowG2 P :=
  ⟨3, 1, by norm_num, h⟩

theorem Thm3RowsA.toRowsG {Ω : Set (Subgroup Y)} {P : Subgroup Y} (h : Thm3RowsA Ω P) :
    Thm3RowsG Ω P := Or.inr h

end Rows

section Theorem

@[expose] def Thm3RConclG {Y : Type} [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (K : Subgroup Y) :
    Prop :=
  (aStar Φ K = vStar Φ K ∧
      ∀ L ∈ Φ, L ∉ vStar Φ K → ∀ M ∈ vStar Φ K, ⁅L, M⁆ ≤ oddCoreOf L ⊓ oddCoreOf M) ∧
    Thm3RowsG Φ (omegaGen (aStar Φ K))

end Theorem

end Thm3A

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
