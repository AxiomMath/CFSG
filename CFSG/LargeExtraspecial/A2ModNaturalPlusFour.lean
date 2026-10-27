module

public import CFSG.LargeExtraspecial.A2ModNaturalHub
public import CFSG.LargeExtraspecial.AS35YUHub

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module QuadraticMap CFSG.Open CFSG.Blueprint Matrix

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}


theorem exists_natural_pOmegaPlus_four [Finite X] (hD : RootClass X D) (hA : A2Action D Q ρ)
    (hL : LieModel X .POmegaPlus 4 2 1) :
    ∃ (φ : X ≃* ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2))))
      (π : V →ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)),
      (commSpaceOf ρ ⊤).map π = ⊤ ∧ commSpaceOf ρ ⊤ ⊓ LinearMap.ker π = ⊥ ∧
      (∀ x, ∀ v ∈ commSpaceOf ρ ⊤, π (ρ x v) =
        ((φ x : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2))
          *ᵥ π v) ∧
      (∀ v ∈ commSpaceOf ρ ⊤, StatedQuadPlus 4 (ZMod 2) (π v) = Q v) := by
  have hdim := AS35YU.dim_le_eight_of_pomega4_YU hD hA (Or.inl hL)
  have := (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus X 4 2 1
    (Ord.statedClassicalModel_of_lieModel (by decide) hL)).2
  exact Natural.exists_natural_plus hA.nondegenerate hA.map_apply hA.injective hD.2.2.2
    hD.commutator_eq_top le_rfl (Ord.card_of_lieModel_POmegaPlus hL).2
    (AS35YT.spOrd_pred_lt_card_of_lieModel_POmega (Or.inl hL)) hdim

end CFSG.LargeExtraspecial.A2Mod
