module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualMatrixSeparate
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualMain

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect)
open LinearPilot (autFixSubgroup mem_autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus commutator_coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Cases

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

@[expose] def SymmetryCoresRigid (n : ℕ) (K : Type) [Field K]
    (fp : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)) →* (K ≃+* K)) : Prop :=
  ∀ v₁ v₂ : Fin (2 * n) → K, coordinateQuadPlus n K v₁ = 1 → coordinateQuadPlus n K v₂ = 1 →
    FieldRigidInOf fp (perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v₁)))
      (perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v₂)))

@[expose] def HigherRankCoresRigid (n : ℕ) (K : Type) [Field K]
    (fp : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)) →* (K ≃+* K)) : Prop :=
  ∀ s₁ s₂ : matrixIsometries (coordinateQuadPlus n K),
    orderOf (isometryConjugationHom _ s₁) = 2 → orderOf (isometryConjugationHom _ s₂) = 2 →
    2 ≤ (((s₁ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank →
    2 ≤ (((s₂ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank →
    FieldRigidInOf fp (perfectCore (autFixSubgroup (isometryConjugationHom _ s₁)))
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s₂)))

theorem fieldRigidInOf_of_simple_not_simple {C : Type*} [Group C] {L : Type*} [Field L]
    (fp : MulAut C →* (L ≃+* L)) {X₁ X₂ : Subgroup C}
    (h : IsSimpleGroup ↥X₁ ∧ ¬ IsSimpleGroup ↥X₂ ∨ ¬ IsSimpleGroup ↥X₁ ∧ IsSimpleGroup ↥X₂) :
    FieldRigidInOf fp X₁ X₂ := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX
  exfalso
  have e : ↥X₁ ≃* ↥X₂ := (X₁.equivMapOfInjective φ₁ hφ₁).trans
    ((MulEquiv.subgroupCongr hX).trans (X₂.equivMapOfInjective φ₂ hφ₂).symm)
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (@MulEquiv.isSimpleGroup _ _ _ _ h1 e.symm)
  · exact h1 (@MulEquiv.isSimpleGroup _ _ _ _ h2 e)

theorem nonFieldCoresRigid_plus_of_cases (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (hsym : SymmetryCoresRigid n K (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn))
    (hhigh : HigherRankCoresRigid n K
      (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)) :
    NonFieldCoresRigid (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn) := by
  intro α₁ α₂ h₁ h₂ hne₁ hne₂ hfp₁ hfp₂
  rcases nonField_cases hK hn h₁ hne₁ hfp₁ with ⟨v₁, hv₁, rfl⟩ | ⟨s₁, rfl, hs₁, hr₁⟩ <;>
    rcases nonField_cases hK hn h₂ hne₂ hfp₂ with ⟨v₂, hv₂, rfl⟩ | ⟨s₂, rfl, hs₂, hr₂⟩
  · exact hsym v₁ v₂ hv₁ hv₂
  · exact fieldRigidInOf_of_simple_not_simple _ (Or.inl
      ⟨(symmetryCore_spec hK hn hv₁).1, not_isSimpleGroup_core_of_two_le_rank hn s₂ hs₂ hr₂⟩)
  · exact fieldRigidInOf_of_simple_not_simple _ (Or.inr
      ⟨not_isSimpleGroup_core_of_two_le_rank hn s₁ hs₁ hr₁, (symmetryCore_spec hK hn hv₂).1⟩)
  · exact hhigh s₁ s₂ hs₁ hs₂ hr₁ hr₂

end Cases

section Read

variable {C : Type*} [Group C] [Finite C] {L : Type*} [Field L] [Finite L]

@[expose] noncomputable def restrictAutOfMapsTo (β : MulAut C) (X : Subgroup C)
    (hX : ∀ x ∈ X, β x ∈ X) : MulAut ↥X :=
  MulEquiv.ofBijective (((β.toMonoidHom.comp X.subtype).codRestrict X fun x => hX x x.2))
    (by
      have hinj : Function.Injective
          (((β.toMonoidHom.comp X.subtype).codRestrict X fun x => hX x x.2)) :=
        fun x y h => Subtype.ext (β.injective (congrArg Subtype.val h))
      exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩)

theorem coe_restrictAutOfMapsTo (β : MulAut C) (X : Subgroup C) (hX : ∀ x ∈ X, β x ∈ X) (x : X) :
    ((restrictAutOfMapsTo β X hX x : X) : C) = β x := rfl

end Read

section Input

theorem omegaPlusResidualMatrixInput_of_nonFieldCoresRigid
    (hFR : ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
      (hn : 5 ≤ n), Even f →
        NonFieldCoresRigid (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)) :
    OmegaPlusResidualMatrixInput := fun n f K _ _ _ hK hn hfe =>
  ⟨hFR n f K hK hn hfe, fieldRecentreIn_plus hK hn⟩

end Input

end CFSG.SeitzReduction.OmegaPilot
