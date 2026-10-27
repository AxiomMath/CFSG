module

public import CFSG.LargeExtraspecial.A2ModNDefs
public import CFSG.LargeExtraspecial.A2ModD4Main
public import CFSG.LargeExtraspecial.DWInsCert
public import CFSG.LargeExtraspecial.DWInsMain
public import CFSG.LargeExtraspecial.DWInsT

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def DW2OutInspectionInputN : Prop :=
  DW2FieldInput ∧
  (∀ (X : Type) [Group X] [Finite X], NativeSporadic.IsSporadic X .J2 → IsPGroup 2 (Outer X)) ∧
  (∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (q : QuadraticForm (ZMod 2) V), q.polarBilin.Nondegenerate →
      ∀ X Y : Subgroup (V ≃ₗ[ZMod 2] V), (∀ y ∈ Y, ∀ v, q (y v) = q v) → X ≤ Y →
        Y ≤ normalizer (X : Set (V ≃ₗ[ZMod 2] V)) → LieModel X .POmegaPlus 4 2 1 →
        ∀ D : Set (V ≃ₗ[ZMod 2] V), X = closure D →
          (∃ d₀ ∈ D, ∀ d, d ∈ D ↔ ∃ g ∈ X, d = g * d₀ * g⁻¹) → (∀ d ∈ D, IsTypeA q d 2) →
          ∀ y ∈ Y, ∃ k : ℕ, ∃ x ∈ X, ∃ c ∈ Y, (∀ x' ∈ X, c * x' = x' * c) ∧
            y ^ 2 ^ k = x * c) ∧
  DW2ModuleInputD4 ∧ S12ExcModuleInputN

namespace DW2OutInspectionInputN

variable (h : DW2OutInspectionInputN)
include h

theorem field : DW2FieldInput := h.1

theorem outerJ2 :
    ∀ (X : Type) [Group X] [Finite X], NativeSporadic.IsSporadic X .J2 → IsPGroup 2 (Outer X) :=
  h.2.1

theorem moduleD4 : DW2ModuleInputD4 := h.2.2.2.1

theorem moduleExc : S12ExcModuleInputN := h.2.2.2.2

end DW2OutInspectionInputN

theorem dw2OutInspectionInputN_of_cert
    (hF : DW2FieldInput)
    (hE : S12ExcModuleInputN) : DW2OutInspectionInputN :=
  ⟨hF, dw2Out_clauseO, dw2Out_clauseT dw27Check_eq_true, A2Mod.d42_commSpace, hE⟩

end CFSG.LargeExtraspecial.DW
