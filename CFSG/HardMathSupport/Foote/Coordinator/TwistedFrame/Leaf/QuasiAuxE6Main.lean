module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxMain
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxE6X2

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups

set_option linter.unusedSectionVars false


@[expose] def E6ScStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K → 3 ∣ Nat.card K - 1 →
    ∀ (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) (a b : SL(3, D.L)),
      (∀ A B : SL(3, D.L),
        QuasiE6X2.muGL D.L (a * Matrix.SpecialLinearGroup.map D.Fr B * a⁻¹,
            b * Matrix.SpecialLinearGroup.map D.Fr A * b⁻¹) =
          D.nW * D.frobGL (QuasiE6X2.muGL D.L (A, B)) * D.nW⁻¹) →
      ∀ y ∈ D.frameImage (TwClass.S₂ TwClass.e6Six),
        ∃ s : SL(3, D.L) × SL(3, D.L),
          (a * Matrix.SpecialLinearGroup.map D.Fr s.2 * a⁻¹,
            b * Matrix.SpecialLinearGroup.map D.Fr s.1 * b⁻¹) = s ∧ QuasiE6X2.muGL D.L s = y

theorem e6SixX₂_of_sc (hsc : E6ScStatement) : E6SixX₂Statement := by
  intro K _ _ hK D
  obtain ⟨a, b, P, hab, hPle, hPqs, -, hPeq, hexact⟩ := QuasiE6X2.exch_data hK D
  have hP1 : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.mp hPqs.1
  have hge : P ≤ D.frameImage (TwClass.S₂ TwClass.e6Six) := D.le_frameImage_of_perfect hPle hP1
  have hle : D.frameImage (TwClass.S₂ TwClass.e6Six) ≤ P := by
    by_cases h3 : 3 ∣ Nat.card K - 1
    · intro y hy
      obtain ⟨s, hs, rfl⟩ := hsc K hK h3 D a b hab y hy
      exact hexact s hs
    · rw [hPeq h3]
      exact D.frameImage_le_fixedRoot _
  exact D.isQuasisimple_frame_of_frameImage_eq (le_antisymm hle hge) hPqs

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
