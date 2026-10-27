module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.ComponentClassification.AschbacherTheorem3

@[expose] def Asc82InputDihSd : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (D : Subgroup E), IsDihedralTwoGroup D → 8 ≤ Nat.card D →
    (∀ x ∈ normalizer (D : Set E), x ∉ D → orderOf x = 2 →
      ∀ d ∈ D, orderOf d = 2 → ∀ g : E, g⁻¹ * x * g ≠ d) →
    ∀ P : Subgroup E, CFSG.ABGLocalTools.IsSylowOf 2 P (normalClosure (D : Set E)) →
      IsDihedralTwoGroup P ∨ IsSemidihedralTwoGroup P

end CFSG.OddStandard.SmallF3.Omega
