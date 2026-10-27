module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBIsometry
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherRigidity
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBLinearHigherB

@[expose] def KAL4Split {F : Type} [Field F] (A : GL (Fin 4) F) : Prop :=
  ∃ S : Submodule F (Fin 4 → F), Module.finrank F ↥S = 2 ∧
    ∀ x ∈ S, matrixQuadraticForm (A⁻¹ : GL (Fin 4) F) x = 0

theorem ka_ringChar_ne_two_of_card_three {F : Type} [Field F] [Finite F]
    (h3 : Nat.card F = 3) : ringChar F ≠ 2 := by
  intro h
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  rw [← Nat.card_eq_fintype_card, h3, h] at hn
  have h2 : 2 ∣ 2 ^ (n : ℕ) := dvd_pow_self 2 n.pos.ne'
  rw [← hn] at h2
  omega

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
