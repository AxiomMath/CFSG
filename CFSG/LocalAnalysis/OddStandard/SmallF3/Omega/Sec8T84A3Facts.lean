module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def Sec8T84FactA5 : Prop :=
  ∀ (G : Type) [Group G] (B : Subgroup G), IsElemAb2 B 4 → ∀ H : Subgroup (MulAut ↥B),
    Nonempty (↥H ≃* alternatingGroup (Fin 6)) →
      ∃ H5 : Subgroup (MulAut ↥B), H5 ≤ H ∧ Nonempty (↥H5 ≃* alternatingGroup (Fin 5)) ∧
        ∀ x : ↥B, x ≠ 1 → ∀ y : ↥B, y ≠ 1 → ∃ h ∈ H5, h x = y

@[expose] def Sec8T84FactS6 : Prop :=
  ∀ (G : Type) [Group G] (B : Subgroup G), IsElemAb2 B 4 →
    ∀ H₁ H₀ : Subgroup (MulAut ↥B), H₁ ≤ H₀ → Nonempty (↥H₁ ≃* alternatingGroup (Fin 6)) →
      Nonempty (↥H₀ ≃* Equiv.Perm (Fin 6)) →
        ∃ x ∈ H₀, x ∉ H₁ ∧ x * x = 1 ∧ Nat.card {b : ↥B // x b = b} = 8 ∧
          ∃ w ∈ H₁, w ^ 3 = 1 ∧ Nat.card {b : ↥B // w b = b} = 4 ∧ x * w = w * x ∧
            (∀ c : ↥B, w (x c * c⁻¹) = x c * c⁻¹) ∧
            ∀ b : ↥B, w b = b → x b = b → ∃ c : ↥B, b = x c * c⁻¹

@[expose] def Sec8T84FactInv : Prop :=
  ∀ (G : Type) [Group G] (B : Subgroup G), IsElemAb2 B 4 → ∀ H : Subgroup (MulAut ↥B),
    Nonempty (↥H ≃* alternatingGroup (Fin 6)) →
      ∀ x ∈ H, x ≠ 1 → x * x = 1 → Nat.card {b : ↥B // x b = b} = 4

end CFSG.OddStandard.SmallF3.Omega
