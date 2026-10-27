module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFamily
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HarrisLit.L33

open CFSG Subgroup

@[expose] def L33For (C : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], C Y → HarrisF 3 Y → ∀ a : MulAut Y, orderOf a = 2 →
    IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) →
      ∃ m : ℕ, 2 ≤ m ∧ Blueprint.LieModel Y .PSL 2 3 m

@[expose] def IsTwoNilpExc (Y : Type) [Group Y] : Prop :=
  (∃ p f : ℕ, Blueprint.LieModel Y .PSL 2 p f) ∨ (∃ p f : ℕ, Blueprint.SuzukiModel Y p f) ∨
    Blueprint.LieModel Y .PSL 3 2 2 ∨ Blueprint.LieModel Y .PSU 3 2 2 ∨
    Nonempty (Y ≃* alternatingGroup (Fin 7))

@[expose] def TwoNilpFor (C : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], C Y → IsSimpleGroup Y → (∃ x y : Y, x * y ≠ y * x) →
    ∀ a : MulAut Y, orderOf a = 2 →
      IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) → IsTwoNilpExc Y

end CFSG.ComponentClassification.HarrisLit.L33
