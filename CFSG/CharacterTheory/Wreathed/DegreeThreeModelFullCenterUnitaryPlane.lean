module

public import CFSG.CharacterTheory.Wreathed.OddUnitaryThreeCentralizerCore
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenterScalars

public noncomputable section

namespace CFSG.Wreathed.DegreeThreeModelFullCenter

open Matrix CFSG.ComponentClassification
open CatalogueBUnitaryIsometry CatalogueBUnitaryTwo
open OddUnitaryThreeCentralizerCore
open CFSG.Semidihedral.OddLinearNormals
open CFSG.LocalAnalysis.ComponentInitial

universe u v w

variable {E : Type u} [Field E] {V : Type v} [AddCommGroup V] [Module E V]

theorem planeCoordinates_scalar (B : (Fin 2 → E) ≃ₗ[E] V) (c : Eˣ) :
    planeCoordinates B (LinearEquiv.smulOfUnit c) =
      GeneralLinearGroup.scalar (Fin 2) c := by
  apply Units.ext
  rw [planeCoordinates_val]
  have he : ((B.trans (LinearEquiv.smulOfUnit c)).trans B.symm).toLinearMap =
      (c : E) • LinearMap.id := by
    apply LinearMap.ext
    intro x
    change B.symm ((c : E) • B x) = (c : E) • x
    rw [B.symm.map_smul, B.symm_apply_apply]
  rw [he, map_smul, LinearMap.toMatrix'_id, GeneralLinearGroup.coe_scalar]
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

section OriginalUnitaryPlane

variable {sigma : E ≃+* E} (h : V →ₛₗ[sigma.toRingHom] V →ₗ[E] E)

@[expose] def unitaryPlaneMatrixHom (B : (Fin 2 → E) ≃ₗ[E] V) :
    isometryGroup h →* GeneralLinearGroup (Fin 2) E :=
  (planeCoordinates B).toMonoidHom.comp (isometryGroup h).subtype

theorem unitaryPlaneMatrixHom_val (B : (Fin 2 → E) ≃ₗ[E] V) (g : isometryGroup h) :
    (unitaryPlaneMatrixHom h B g).val =
      LinearMap.toMatrix' ((B.trans g.val).trans B.symm).toLinearMap :=
  planeCoordinates_val B g.val

theorem unitaryPlaneMatrixHom_injective (B : (Fin 2 → E) ≃ₗ[E] V) :
    Function.Injective (unitaryPlaneMatrixHom h B) :=
  (planeCoordinates B).injective.comp Subtype.val_injective

@[expose] def unitaryPlaneMatrixEquiv (B : (Fin 2 → E) ≃ₗ[E] V) :
    isometryGroup h ≃* (unitaryPlaneMatrixHom h B).range :=
  MonoidHom.ofInjective (unitaryPlaneMatrixHom_injective h B)

theorem unitaryPlaneMatrixEquiv_coe (B : (Fin 2 → E) ≃ₗ[E] V) (g : isometryGroup h) :
    (unitaryPlaneMatrixEquiv h B g : GeneralLinearGroup (Fin 2) E) =
      unitaryPlaneMatrixHom h B g := rfl

theorem unitaryPlaneMatrixHom_scalar (B : (Fin 2 → E) ≃ₗ[E] V)
    (c : normOneUnits (sigma := sigma)) :
    unitaryPlaneMatrixHom h B (scalarIsometry h c) =
      GeneralLinearGroup.scalar (Fin 2) c.val :=
  planeCoordinates_scalar B c.val

@[expose] def unitaryMatrixScalarHom (B : (Fin 2 → E) ≃ₗ[E] V) :
    normOneUnits (sigma := sigma) →* (unitaryPlaneMatrixHom h B).range :=
  (unitaryPlaneMatrixEquiv h B).toMonoidHom.comp (scalarIsometry h)

theorem unitaryMatrixScalarHom_coe (B : (Fin 2 → E) ≃ₗ[E] V)
    (c : normOneUnits (sigma := sigma)) :
    (unitaryMatrixScalarHom h B c : GeneralLinearGroup (Fin 2) E) =
      GeneralLinearGroup.scalar (Fin 2) c.val :=
  unitaryPlaneMatrixHom_scalar h B c

theorem unitaryPlaneMatrixEquiv_symm_scalar (B : (Fin 2 → E) ≃ₗ[E] V)
    (c : normOneUnits (sigma := sigma)) :
    (unitaryPlaneMatrixEquiv h B).symm (unitaryMatrixScalarHom h B c) =
      scalarIsometry h c :=
  (unitaryPlaneMatrixEquiv h B).symm_apply_apply (scalarIsometry h c)

theorem unitaryPlaneMatrixEquiv_symm_comp_scalars (B : (Fin 2 → E) ≃ₗ[E] V) :
    (unitaryPlaneMatrixEquiv h B).symm.toMonoidHom.comp (unitaryMatrixScalarHom h B) =
      scalarIsometry h := by
  apply MonoidHom.ext
  intro c
  exact unitaryPlaneMatrixEquiv_symm_scalar h B c

theorem unitaryMatrixScalarHom_injective (B : (Fin 2 → E) ≃ₗ[E] V) :
    Function.Injective (unitaryMatrixScalarHom h B) := by
  let : Nontrivial V := B.symm.nontrivial
  exact (unitaryPlaneMatrixEquiv h B).injective.comp (scalarIsometry_injective h)

theorem unitaryMatrixScalarHom_range (hnd : h.Nondegenerate)
    (B : (Fin 2 → E) ≃ₗ[E] V) :
    (unitaryMatrixScalarHom h B).range = scalarSubgroup (unitaryPlaneMatrixHom h B).range := by
  let : Nontrivial V := B.symm.nontrivial
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    change unitaryPlaneMatrixHom h B (scalarIsometry h c) ∈
      Subgroup.center (GeneralLinearGroup (Fin 2) E)
    rw [unitaryPlaneMatrixHom_scalar, GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c.val, rfl⟩
  · intro hg
    obtain ⟨a, rfl⟩ := (unitaryPlaneMatrixEquiv h B).surjective g
    change unitaryPlaneMatrixHom h B a ∈ Subgroup.center (GeneralLinearGroup (Fin 2) E) at hg
    rw [GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨c, hc⟩ := hg
    have hscalar : a.val = LinearEquiv.smulOfUnit c := by
      apply (planeCoordinates B).injective
      exact hc.symm.trans (planeCoordinates_scalar B c).symm
    have hciso : scalarAction c ∈ isometryGroup h := by
      change LinearEquiv.smulOfUnit c ∈ isometryGroup h
      rw [← hscalar]
      exact a.property
    have hcnorm := scalar_norm_one_of_isometry h hnd c hciso
    refine ⟨⟨c, hcnorm⟩, ?_⟩
    change unitaryPlaneMatrixEquiv h B (scalarIsometry h ⟨c, hcnorm⟩) = _
    congr 1
    apply Subtype.ext
    exact hscalar.symm

theorem unitaryPlaneMatrixHom_contains_special (B : (Fin 2 → E) ≃ₗ[E] V) (t : Eˣ)
    (e : specialIsometry h ≃*
      SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma))
    (hinverse : ∀ N, LinearMap.toMatrix'
      ((B.trans (e.symm N).val.val).trans B.symm).toLinearMap =
        (diagonalGL t).val * (fixedSLMap sigma N).val * (diagonalGL t)⁻¹.val) :
    conjugatedImageSL (CatalogueBLinearTwoDescent.fixedSubfield E sigma).subtype
      (diagonalGL t) ≤ (unitaryPlaneMatrixHom h B).range := by
  rw [planeCoordinates_special_range h B t e hinverse]
  rintro g ⟨a, rfl⟩
  exact ⟨a.val, rfl⟩

@[expose] def unitaryPlaneNativeEquiv : isometryGroup h ≃* sesqUnitaryGroup h where
  toFun g := ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv E V).symm g.val, g.property⟩
  invFun g := ⟨LinearMap.GeneralLinearGroup.generalLinearEquiv E V g.val, g.property⟩
  left_inv g :=
    Subtype.ext ((LinearMap.GeneralLinearGroup.generalLinearEquiv E V).apply_symm_apply g.val)
  right_inv g :=
    Subtype.ext ((LinearMap.GeneralLinearGroup.generalLinearEquiv E V).symm_apply_apply g.val)
  map_mul' g j :=
    Subtype.ext ((LinearMap.GeneralLinearGroup.generalLinearEquiv E V).symm.map_mul g.val j.val)

end OriginalUnitaryPlane

section OriginalUnitaryPlaneOrder

variable [Finite E] [FiniteDimensional E V]

theorem unitaryPlane_order (p f : ℕ) [Fact p.Prime]
    (hE : Nat.card E = (p ^ f) ^ 2)
    (h : V →ₛₗ[(unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (hdim : Module.finrank E V = 2) :
    Nat.card (isometryGroup h) = p ^ f * ((p ^ f) ^ 2 - 1) * (p ^ f + 1) := by
  let data := originalFieldData p f hE
  have he := originalFieldData_bar p f hE
  let hNative : V →ₛₗ[data.bar] V →ₗ[E] E :=
    { toFun := h
      map_add' := h.map_add'
      map_smul' := by
        intro c x
        rw [← he]
        exact h.map_smul' c x }
  have hNativeSymm : hNative.IsSymm := ⟨fun x y => by
    change data.bar (h x y) = h y x
    rw [← he]
    exact hsym.eq x y⟩
  have hNativeNd : hNative.SeparatingLeft := hnd.1
  have hNativeGroup : sesqUnitaryGroup hNative = sesqUnitaryGroup h := by
    ext g
    rfl
  have hc := (CFSG.LinearGroups.unitary_full_group_order
    data hNativeSymm hNativeNd hdim (by decide)).1
  rw [hNativeGroup] at hc
  have hU : (Nat.card (isometryGroup h) : ℤ) =
      (p ^ f : ℕ) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * ((p ^ f : ℕ) + 1) := by
    rw [Nat.card_congr (unitaryPlaneNativeEquiv h).toEquiv]
    have hset : Finset.Icc 1 2 = {1, 2} := by decide
    rw [hset] at hc
    simp only [show 2 * (2 - 1) / 2 = 1 by decide, pow_one, Finset.prod_insert,
      Finset.mem_singleton, show (1 : ℕ) ≠ 2 by decide, not_false_eq_true,
      Finset.prod_singleton, neg_one_sq] at hc
    exact hc.trans (by ring)
  have hq : 1 ≤ p ^ f := one_le_pow₀ (Fact.out : p.Prime).one_le
  have hq2 : 1 ≤ (p ^ f) ^ 2 := one_le_pow₀ hq
  zify [hq2]
  exact hU

omit [FiniteDimensional E V] in
theorem card_unitaryMatrixScalars (p f : ℕ) [Fact p.Prime]
    (hE : Nat.card E = (p ^ f) ^ 2)
    (h : V →ₛₗ[(unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E)
    (hnd : h.Nondegenerate) (B : (Fin 2 → E) ≃ₗ[E] V) :
    Nat.card (scalarSubgroup (unitaryPlaneMatrixHom h B).range) = p ^ f + 1 := by
  rw [← unitaryMatrixScalarHom_range h hnd B,
    ← Nat.card_congr (MonoidHom.ofInjective (unitaryMatrixScalarHom_injective h B)).toEquiv]
  exact normOneUnits_card p f hE

theorem card_unitaryPlaneMatrixGroup (p f : ℕ) [Fact p.Prime]
    (hE : Nat.card E = (p ^ f) ^ 2)
    (h : V →ₛₗ[(unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (hdim : Module.finrank E V = 2)
    (B : (Fin 2 → E) ≃ₗ[E] V) :
    Nat.card (unitaryPlaneMatrixHom h B).range =
      Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E (unitaryFieldConjugation p f hE)) *
        (Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E (unitaryFieldConjugation p f hE)) ^
          2 - 1) * Nat.card (scalarSubgroup (unitaryPlaneMatrixHom h B).range) := by
  rw [← Nat.card_congr (unitaryPlaneMatrixEquiv h B).toEquiv,
    unitaryPlane_order p f hE h hsym hnd hdim, card_unitaryMatrixScalars p f hE h hnd B,
    (unitaryFieldConjugation_data p f hE).2.2]

end OriginalUnitaryPlaneOrder

end CFSG.Wreathed.DegreeThreeModelFullCenter
