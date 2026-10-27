module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82NormA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G), IsElemAb2 B 4 →
    ∀ H₁ H₂ : Subgroup (MulAut ↥B), H₁ ≤ H₂ → Nonempty (↥H₁ ≃* alternatingGroup (Fin 6)) →
      (∀ h ∈ H₂, ∀ a ∈ H₁, h * a * h⁻¹ ∈ H₁) →
        Nonempty (↥H₂ ≃* alternatingGroup (Fin 6)) ∨ Nonempty (↥H₂ ≃* Equiv.Perm (Fin 6))

end CFSG.OddStandard.SmallF3.Omega
