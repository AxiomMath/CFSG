module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheck
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.U3

open CFSG.ClassicalInvolution.Q3.TA3.Check

variable {M : Type} [Group M] [DecidableEq M]

@[expose] def ExitFacts (P A : Subgroup M) (t : M) : Prop :=
  (∀ a b a' b' : M, (a ∈ A ∧ b ∈ A ∧ a * a = t ∧ b * b = t ∧ b * a = t * a * b) →
      (a' ∈ A ∧ b' ∈ A ∧ a' * a' = t ∧ b' * b' = t ∧ b' * a' = t * a' * b') →
      ((a ∈ P ∧ b ∈ P) ↔ (a' ∈ P ∧ b' ∈ P)) → ∀ x ∈ q8B t a b, x ∈ q8B t a' b') ∧
    ∃ ao bo ai bi g : M, (ao ∈ A ∧ bo ∈ A ∧ ao * ao = t ∧ bo * bo = t ∧ bo * ao = t * ao * bo) ∧
      ¬(ao ∈ P ∧ bo ∈ P) ∧
      (ai ∈ A ∧ bi ∈ A ∧ ai * ai = t ∧ bi * bi = t ∧ bi * ai = t * ai * bi) ∧
      ai ∈ P ∧ bi ∈ P ∧ g ∈ A ∧
      (∃ c ∈ q8B t ao bo, c * c = t ∧ g * c * g⁻¹ * t = t * (g * c * g⁻¹)) ∧
      ∃ d ∈ q8B t ao bo, ∃ x ∈ q8B t ai bi, g * d * g⁻¹ * x * (g * d * g⁻¹)⁻¹ ∉ q8B t ai bi

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.U3
