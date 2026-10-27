module

public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup

@[expose] def GorensteinHaradaThmCInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], pPrimeCore 2 X = ⊥ →
    letI : (pCore 2 X).Normal := pCore_normal
    ∀ T : Sylow 2 X, Nonempty ((T : Subgroup X) ≃* GH74.GLS.Bg.TwoGroups.SylSL3_4) →
    (∃ u v : X, orderOf u = 2 ∧ orderOf v = 2 ∧ ¬ IsConj u v) →
    centralizer (pCore 2 X : Set X) ≤ pCore 2 X ∧
      ((pCore 2 X = T ∧ (T : Subgroup X).index ∣ 9 ∧
          ∀ B : Subgroup X, B ≤ T → (∀ b ∈ B, b * b = 1) →
            (∀ b ∈ B, ∀ c ∈ B, b * c = c * b) → Nat.card B = 16 → B.Normal) ∨
        ((pCore 2 X : Subgroup X) ≤ T ∧ Nat.card (pCore 2 X) = 16 ∧
          (∀ b ∈ pCore 2 X, b * b = 1) ∧ (∀ b ∈ pCore 2 X, ∀ c ∈ pCore 2 X, b * c = c * b) ∧
          (Nonempty (X ⧸ pCore 2 X ≃* alternatingGroup (Fin 5)) ∨
            Nonempty (X ⧸ pCore 2 X ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5))) ∧
          ∀ u ∈ pCore 2 X, ∀ v ∈ pCore 2 X, u ≠ 1 → v ≠ 1 → ∃ g : X, g⁻¹ * u * g = v))

end CFSG.ComponentClassification.GHarris
