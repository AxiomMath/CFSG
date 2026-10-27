module

public import CFSG.LargeExtraspecial.AS35QThGU
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QTh

open QuadraticMap Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {ζ : V →ₗ[ZMod 2] V} {l : (Fin 3 → K) → V}

namespace HermCoords

variable (hl : HermCoords q ζ l)
include hl

theorem thetaMat_eq_iff (σ : V →ₗ[ZMod 2] V) (hσ : ∀ v, σ (ζ v) = ζ (σ v))
    (A : Matrix (Fin 3) (Fin 3) K) :
    hl.thetaMat σ hσ = A ↔ ∀ x, l (A *ᵥ x) = σ (l x) := by
  constructor
  · rintro rfl x
    exact hl.l_thetaMat_mulVec σ hσ x
  · intro h
    refine Matrix.ext_of_mulVec_single fun j => ?_
    apply hl.bij.1
    rw [hl.l_thetaMat_mulVec, h]

variable (H : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q))
  (hH : ∀ σ ∈ H, ∀ v, ((σ : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[ZMod 2] V) (ζ v) =
    ζ (((σ : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[ZMod 2] V) v))

@[expose] noncomputable def thetaH (σ : H) : Matrix (Fin 3) (Fin 3) K :=
  hl.thetaMat ((σ : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[ZMod 2] V).toLinearMap
    (hH σ σ.2)

theorem l_thetaH (σ : H) (x : Fin 3 → K) :
    l (hl.thetaH H hH σ *ᵥ x) = ((σ : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[ZMod 2] V)
      (l x) :=
  hl.l_thetaMat_mulVec _ _ x

theorem conjTr_thetaH (σ : H) : conjTr frob (hl.thetaH H hH σ) * hl.thetaH H hH σ = 1 :=
  hl.conjTr_thetaMat _ _ fun v =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (σ : TauCeti.QuadraticMap.orthogonalGroup q).2 v

@[expose] noncomputable def thetaGU (σ : H) : GU3 :=
  ⟨⟨hl.thetaH H hH σ, conjTr frob (hl.thetaH H hH σ),
    mul_eq_one_comm.mp (hl.conjTr_thetaH H hH σ), hl.conjTr_thetaH H hH σ⟩,
    hl.conjTr_thetaH H hH σ⟩

theorem l_gv_thetaGU (σ : H) (x : Fin 3 → K) :
    l (gv (hl.thetaGU H hH σ) x) =
      ((σ : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[ZMod 2] V) (l x) :=
  hl.l_thetaH H hH σ x

theorem thetaGU_eq_iff (σ : H) (A : GU3) :
    hl.thetaGU H hH σ = A ↔ ∀ x, l (gv A x) =
      ((σ : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[ZMod 2] V) (l x) := by
  constructor
  · rintro rfl x
    exact hl.l_thetaH H hH σ x
  · intro h
    have e : hl.thetaH H hH σ = gm A := (hl.thetaMat_eq_iff _ _ _).mpr h
    exact Subtype.ext (Units.ext e)

@[expose] noncomputable def thetaHom : H →* GU3 where
  toFun := hl.thetaGU H hH
  map_one' := by
    rw [thetaGU_eq_iff]
    intro x
    rw [gv_one]
    rfl
  map_mul' σ τ := by
    rw [thetaGU_eq_iff]
    intro x
    rw [gv_mul, hl.l_gv_thetaGU, hl.l_gv_thetaGU]
    rfl

theorem l_gv_thetaHom (σ : H) (x : Fin 3 → K) :
    l (gv (hl.thetaHom H hH σ) x) =
      ((σ : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[ZMod 2] V) (l x) :=
  hl.l_thetaH H hH σ x

theorem thetaHom_injective : Function.Injective (hl.thetaHom H hH) := by
  intro σ τ h
  have e : hl.thetaH H hH σ = hl.thetaH H hH τ := by
    have := congrArg gm h
    exact this
  have e' := hl.thetaMat_injective _ _ e
  exact Subtype.ext (Subtype.ext (LinearEquiv.toLinearMap_injective e'))

include hH in
theorem card_le : Nat.card H ≤ 648 :=
  (Nat.card_le_card_of_injective _ (hl.thetaHom_injective H hH)).trans card_GU3_le

end HermCoords

end CFSG.LargeExtraspecial.AS35QTh
