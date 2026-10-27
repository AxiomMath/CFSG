module


public import Mathlib.RepresentationTheory.Irreducible

public section

namespace CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary

variable {F H V : Type*} [Field F] [Group H] [AddCommGroup V] [Module F V]

@[expose] def imageGroup (ρ : Representation F H V) : Type _ :=
  (ρ.toHomUnits).range

noncomputable instance (ρ : Representation F H V) : Group (imageGroup ρ) :=
  inferInstanceAs (Group (ρ.toHomUnits).range)

@[expose] noncomputable def toImage (ρ : Representation F H V) : H →* imageGroup ρ :=
  (ρ.toHomUnits).rangeRestrict

theorem toImage_surjective (ρ : Representation F H V) : Function.Surjective (toImage ρ) :=
  (ρ.toHomUnits).rangeRestrict_surjective

@[expose] noncomputable def faithful (ρ : Representation F H V) : Representation F (imageGroup ρ) V :=
  (Units.coeHom (Module.End F V)).comp (ρ.toHomUnits).range.subtype

theorem faithful_injective (ρ : Representation F H V) : Function.Injective (faithful ρ) := by
  intro a b h
  apply Subtype.ext
  exact Units.ext h

@[simp]
theorem faithful_toImage (ρ : Representation F H V) (h : H) :
    faithful ρ (toImage ρ h) = ρ h := rfl

theorem irreducible_iff (ρ : Representation F H V) :
    (faithful ρ).IsIrreducible ↔ ρ.IsIrreducible := by
  have invariant_iff (ρ : Representation F H V) (W : Submodule F V) :
      (∀ g : imageGroup ρ, ∀ v ∈ W, faithful ρ g v ∈ W) ↔ (∀ h : H, ∀ v ∈ W, ρ h v ∈ W) := by
    constructor
    · intro hW h v hv
      exact hW (toImage ρ h) v hv
    · intro hW g v hv
      obtain ⟨h, rfl⟩ := toImage_surjective ρ g
      exact hW h v hv
  let subrepresentationOrderIso (ρ : Representation F H V) :
      Subrepresentation ρ ≃o Subrepresentation (faithful ρ) := {
    toFun := fun S => ⟨S.toSubmodule, fun g v hv => (invariant_iff ρ S.toSubmodule).2
      (fun h v hv => S.apply_mem_toSubmodule h hv) g v hv⟩
    invFun := fun S => ⟨S.toSubmodule, fun h v hv => (invariant_iff ρ S.toSubmodule).1
      (fun g v hv => S.apply_mem_toSubmodule g hv) h v hv⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff (subrepresentationOrderIso ρ)).symm

end CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary
