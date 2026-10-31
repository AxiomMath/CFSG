
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Multipliers.L34Data
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers.L34 CFSG.ComponentClassification.GrSLit.L34Facts

def l34BHat {E : Type*} [Group E] (q : E →* Equiv.Perm (Fin 42)) : Set E :=
  {e | q e ∈ T0 ∧ (∀ t ∈ T0, q e * t = t * q e) ∧ e * e = 1}

def l34AHat {E : Type*} [Group E] (q : E →* Equiv.Perm (Fin 42)) : Set E :=
  {e | q e ∈ T0 ∧ ∀ b ∈ l34BHat q, e * b = b * e}

def L34GraphCosetIndexFact : Prop :=
  ∀ y ∈ R, ∀ y' ∈ R, (∀ t ∈ T0, y * t * y⁻¹ ∈ T0) → (∀ t ∈ T0, y' * t * y'⁻¹ ∈ T0) →
    (∀ z ∈ T0, (∀ t ∈ T0, z * t = t * z) → y * z = z * y ∧ y' * z = z * y') →
    y ^ 4 = 1 → y' ^ 4 = 1 → (y * y'⁻¹) ^ 4 = 1 → y ∉ S → y' ∉ S → y * y'⁻¹ ∈ S

end CFSG.ComponentClassification.GrSLit
