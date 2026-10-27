module

public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

public section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup

@[expose] def StronglyClosedE16Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X], pPrimeCore 2 X = ⊥ →
    ∀ T : Sylow 2 X, Nonempty ((T : Subgroup X) ≃* GH74.GLS.Bg.TwoGroups.SylSL3_4) →
    ∀ A : Subgroup X, A ≤ T → Nat.card A = 16 → (∀ a ∈ A, a * a = 1) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (T : Subgroup X) → g⁻¹ * a * g ∈ A) → A.Normal

end CFSG.ComponentClassification.GHarris
