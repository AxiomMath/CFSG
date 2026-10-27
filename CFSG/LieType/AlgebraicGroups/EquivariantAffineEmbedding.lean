module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Map
public import TauCeti.LinearAlgebra.End.FiniteOrder
public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint
public import TauCeti.RingTheory.FiniteType.PointSeparation

public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k]

section Coalgebra
variable {C : Type u} [AddCommGroup C] [Module k C] [Coalgebra k C]

def cyclicClosureThree (f : C →ₗc[k] C) (D : TauCeti.Subcoalgebra k C) :
    TauCeti.Subcoalgebra k C := D ⊔ D.map f ⊔ D.map (f.comp f)

theorem le_cyclicClosureThree (f : C →ₗc[k] C) (D : TauCeti.Subcoalgebra k C) :
    D ≤ cyclicClosureThree f D := le_sup_left.trans le_sup_left

theorem map_cyclicClosureThree (f : C →ₗc[k] C)
    (hf : (f.comp f).comp f = CoalgHom.id k C) (D : TauCeti.Subcoalgebra k C) :
    (cyclicClosureThree f D).map f = cyclicClosureThree f D := by
  have hf' : f.comp (f.comp f) = CoalgHom.id k C := by
    simpa only [CoalgHom.comp_assoc] using hf
  simp only [cyclicClosureThree, TauCeti.Subcoalgebra.map_sup,
    TauCeti.Subcoalgebra.map_map, hf', TauCeti.Subcoalgebra.map_id]
  ac_rfl

theorem finite_cyclicClosureThree (f : C →ₗc[k] C) (D : TauCeti.Subcoalgebra k C)
    [Module.Finite k D.toSubmodule] :
    Module.Finite k (cyclicClosureThree f D).toSubmodule := by
  let : Module.Finite k (D.map f).toSubmodule := TauCeti.Subcoalgebra.map_finite f D
  let : Module.Finite k (D.map (f.comp f)).toSubmodule := TauCeti.Subcoalgebra.map_finite _ D
  let : Module.Finite k (D ⊔ D.map f).toSubmodule := TauCeti.Subcoalgebra.sup_finite _ _
  exact TauCeti.Subcoalgebra.sup_finite _ _

end Coalgebra

section PointAction

variable {H : Type u} [CommRing H] [HopfAlgebra k H]
variable {M N : Type u} [AddCommMonoid M] [Module k M] [TauCeti.Comodule k H M]
variable [AddCommMonoid N] [Module k N] [TauCeti.Comodule k H N]

theorem basePointsRepresentation_naturality (f : TauCeti.Comodule.Hom k H M N)
    (g : WithConv (H →ₐ[k] k)) (m : M) :
    f (TauCeti.Comodule.basePointsRepresentation (H := H) M g m) =
      TauCeti.Comodule.basePointsRepresentation (H := H) N g (f m) := by
  have h := LinearMap.congr_fun (TauCeti.Comodule.baseChange_comp_endOfPoint f g.ofConv)
    ((1 : k) ⊗ₜ[k] m)
  have h' := congrArg (TensorProduct.lid k N) h
  have hlid (t : k ⊗[k] M) :
      TensorProduct.lid k N (f.toLinearMap.baseChange k t) =
        f (TensorProduct.lid k M t) := by
    induction t using TensorProduct.inductionOn with
    | tmul a x => simp [← TauCeti.Comodule.Hom.coe_toLinearMap]
    | add x y hx hy =>
        simpa only [← TauCeti.Comodule.Hom.coe_toLinearMap, map_add] using
          congrArg₂ (· + ·) hx hy
  simpa only [LinearMap.comp_apply, LinearMap.baseChange_tmul, hlid,
    TauCeti.Comodule.Hom.coe_toLinearMap,
    ← TauCeti.Comodule.basePointsRepresentation_apply] using h'

theorem regular_basePointsRepresentation_naturality (f : H →ₐc[k] H)
    (g : WithConv (H →ₐ[k] k)) (x : H) :
    f (TauCeti.Comodule.basePointsRepresentation (H := H) H
      (TauCeti.AlgHom.mapDomain f g) x) =
      TauCeti.Comodule.basePointsRepresentation (H := H) H g (f x) := by
  have h := LinearMap.congr_fun (f.baseChange_comp_endOfPoint_regular g.ofConv)
    ((1 : k) ⊗ₜ[k] x)
  have h' := congrArg (TensorProduct.lid k H) h
  have hlid (t : k ⊗[k] H) :
      TensorProduct.lid k H (f.toLinearMap.baseChange k t) =
        f (TensorProduct.lid k H t) := by
    induction t using TensorProduct.inductionOn with
    | tmul a x => simp [BialgHom.toCoalgHom_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [TauCeti.Comodule.basePointsRepresentation_apply,
    TauCeti.Comodule.basePointsRepresentation_apply]
  have hf : f.toLinearMap = f.toAlgHom.toLinearMap :=
    (BialgHom.toAlgHom_toLinearMap f).symm
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, hlid] at h'
  simpa only [
    TauCeti.AlgHom.mapDomain_apply, WithConv.ofConv_toConv,
    BialgHom.coe_toAlgHom, hf, AlgHom.toLinearMap_apply] using h'

end PointAction

section CoefficientMatrix

variable {H M : Type u} [CommRing H] [HopfAlgebra k H]
variable [AddCommMonoid M] [Module k M] [TauCeti.Comodule k H M]

theorem pointsMulEquiv_coordinateBialgHom_eq_toMatrix
    {n : ℕ} (b : Module.Basis (Fin n) k M) (g : WithConv (H →ₐ[k] k)) :
    (TauCeti.GeneralLinear.pointsMulEquiv n
        (TauCeti.AlgHom.mapDomain (TauCeti.Comodule.coordinateBialgHom (H := H) b) g) :
      Matrix (Fin n) (Fin n) k) =
    LinearMap.toMatrixAlgEquiv b
      (TauCeti.Comodule.basePointsRepresentation (H := H) M g) := by
  rw [TauCeti.AlgHom.mapDomain_apply, AlgHom.pointsMulEquiv_comp_coordinateBialgHom]
  ext i j
  rw [Matrix.map_apply, TauCeti.Comodule.coefficientMatrix_apply,
    LinearMap.toMatrixAlgEquiv_apply]
  exact TauCeti.Comodule.apply_matrixCoefficient g (b.coord i) (b j)

end CoefficientMatrix

theorem isSemisimplePoint_of_pow_eq_one
    {K H : Type u} [CommRing H] [HopfAlgebra k H]
    [Field K] [Algebra k K] (g : WithConv (H →ₐ[k] K)) {n : ℕ}
    (hn : (n : K) ≠ 0) (hg : g ^ n = 1) :
    TauCeti.HopfAlgebra.IsSemisimplePoint g := by
  apply (TauCeti.HopfAlgebra.isSemisimplePoint_iff_forall_isSemisimple_endOfPoint g).mpr
  intro M
  apply TauCeti.End.isSemisimple_of_pow_eq_one hn
  have h := congrArg
    (TauCeti.Comodule.pointsRepresentation (R := k) (H := H) (A := K) M) hg
  simpa only [map_pow, map_one, TauCeti.Comodule.pointsRepresentation_apply] using h

theorem basePointsRepresentation_injective_of_generating_subcoalgebra
    {H : Type u} [CommRing H] [HopfAlgebra k H]
    (D : TauCeti.Subcoalgebra k H) (hgen : Algebra.adjoin k (D : Set H) = ⊤) :
    Function.Injective
      (TauCeti.Comodule.basePointsRepresentation (R := k) (H := H) D.toRegularSubcomodule) := by
  intro g h heq
  apply WithConv.ext
  apply AlgHom.ext_of_adjoin_eq_top hgen
  intro x hx
  let φ : Module.Dual k D.toRegularSubcomodule :=
    (Coalgebra.counit (R := k) (A := H)).comp (SMulMemClass.subtype D.toRegularSubcomodule)
  have hcoeff : TauCeti.Comodule.matrixCoefficient (C := H) φ
      (⟨x, hx⟩ : D.toRegularSubcomodule) = x := by
    exact TauCeti.Comodule.matrixCoefficient_counit_comp_subtype D.toRegularSubcomodule ⟨x, hx⟩
  have hg := TauCeti.Comodule.apply_matrixCoefficient g φ (⟨x, hx⟩ : D.toRegularSubcomodule)
  have hh := TauCeti.Comodule.apply_matrixCoefficient h φ (⟨x, hx⟩ : D.toRegularSubcomodule)
  rw [hcoeff] at hg hh
  rw [hg, hh, heq]

theorem basePointsRepresentation_subcomodule_apply
    {H M : Type u} [CommRing H] [HopfAlgebra k H]
    [AddCommMonoid M] [Module k M] [TauCeti.Comodule k H M]
    (N : TauCeti.Subcomodule k H M) (g : WithConv (H →ₐ[k] k)) (x : N) :
    (TauCeti.Comodule.basePointsRepresentation (H := H) N g x : M) =
      TauCeti.Comodule.basePointsRepresentation (H := H) M g x := by
  simpa only [TauCeti.Subcomodule.subtype_apply] using
    basePointsRepresentation_naturality (TauCeti.Subcomodule.subtype N) g x

section LinearActor
variable {H : Type u} [CommRing H] [HopfAlgebra k H] (σ : H →ₐc[k] H)
variable (hσ : (σ.comp σ).comp σ = BialgHom.id k H)
variable (D : TauCeti.Subcoalgebra k H) (hD : D.map σ.toCoalgHom = D)

local instance : AddCommGroup D.toRegularSubcomodule :=
  Module.addCommMonoidToAddCommGroup k

def coordinateActor : Module.End k D.toRegularSubcomodule where
  toFun x := ⟨σ x, by
    change σ (x : H) ∈ D
    simpa only [hD, BialgHom.toCoalgHom_apply] using
      (TauCeti.Subcoalgebra.mem_map_of_mem σ.toCoalgHom x.property :
        σ (x : H) ∈ D.map σ.toCoalgHom)⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add σ (x : H) y
  map_smul' c x := by
    apply Subtype.ext
    exact σ.toAlgHom.toLinearMap.map_smul c (x : H)

theorem coordinateActor_apply (x : D.toRegularSubcomodule) :
    (coordinateActor σ D hD x : H) = σ x := (rfl)

theorem coordinateActor_bijective (hbij : Function.Bijective σ) :
    Function.Bijective (coordinateActor σ D hD) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply hbij.1
    simpa only [coordinateActor_apply] using congrArg Subtype.val h
  · intro x
    have hx : (x : H) ∈ D.map σ.toCoalgHom := hD.symm ▸ x.property
    obtain ⟨y, hy, hxy⟩ := TauCeti.Subcoalgebra.mem_map.mp hx
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    simpa only [coordinateActor_apply, BialgHom.toCoalgHom_apply] using hxy

def coordinateActorEquivOfBijective (hbij : Function.Bijective σ) :
    D.toRegularSubcomodule ≃ₗ[k] D.toRegularSubcomodule :=
  LinearEquiv.ofBijective (coordinateActor σ D hD)
    (coordinateActor_bijective σ D hD hbij)

theorem coordinateActorEquivOfBijective_toLinearMap (hbij : Function.Bijective σ) :
    (coordinateActorEquivOfBijective σ D hD hbij).toLinearMap =
      coordinateActor σ D hD := (rfl)

include hσ in
theorem coordinateActor_cube : (coordinateActor σ D hD) ^ 3 = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change σ (σ (σ (x : H))) = x
  exact congrArg (fun f : H →ₐc[k] H => f x) hσ

include hσ in
theorem coordinateActor_isSemisimple (h3 : (3 : k) ≠ 0) :
    Module.End.IsSemisimple (coordinateActor σ D hD) :=
  TauCeti.End.isSemisimple_of_pow_eq_one h3 (coordinateActor_cube σ hσ D hD)

theorem coordinateActor_intertwines (g : WithConv (H →ₐ[k] k)) :
    (coordinateActor σ D hD : Module.End k D.toRegularSubcomodule) ∘ₗ
        TauCeti.Comodule.basePointsRepresentation (H := H) D.toRegularSubcomodule
          (TauCeti.AlgHom.mapDomain σ g) =
      TauCeti.Comodule.basePointsRepresentation (H := H) D.toRegularSubcomodule g ∘ₗ
        (coordinateActor σ D hD : Module.End k D.toRegularSubcomodule) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (coordinateActor σ D hD
      (TauCeti.Comodule.basePointsRepresentation (H := H) D.toRegularSubcomodule
        (TauCeti.AlgHom.mapDomain σ g) x) : H) =
    (TauCeti.Comodule.basePointsRepresentation (H := H) D.toRegularSubcomodule g
      (coordinateActor σ D hD x) : H)
  rw [coordinateActor_apply, basePointsRepresentation_subcomodule_apply,
    basePointsRepresentation_subcomodule_apply, coordinateActor_apply]
  exact regular_basePointsRepresentation_naturality σ g x

include hσ in
def coordinateActorEquiv : D.toRegularSubcomodule ≃ₗ[k] D.toRegularSubcomodule :=
  LinearEquiv.ofLinear (coordinateActor σ D hD) ((coordinateActor σ D hD) ^ 2)
    (by simpa only [← Module.End.mul_eq_comp, ← pow_succ', Module.End.one_eq_id] using
      coordinateActor_cube σ hσ D hD)
    (by simpa only [← Module.End.mul_eq_comp, ← pow_succ, Module.End.one_eq_id] using
      coordinateActor_cube σ hσ D hD)

include hσ in
theorem coordinateActorEquiv_toLinearMap :
    (coordinateActorEquiv σ hσ D hD).toLinearMap = coordinateActor σ D hD := (rfl)

include hσ in
theorem coordinateActor_conj (g : WithConv (H →ₐ[k] k)) :
    TauCeti.Comodule.basePointsRepresentation (H := H) D.toRegularSubcomodule
        (TauCeti.AlgHom.mapDomain σ g) =
      (coordinateActorEquiv σ hσ D hD).symm.toLinearMap ∘ₗ
        TauCeti.Comodule.basePointsRepresentation (H := H) D.toRegularSubcomodule g ∘ₗ
        (coordinateActorEquiv σ hσ D hD).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply (coordinateActorEquiv σ hσ D hD).injective
  have h := LinearMap.congr_fun (coordinateActor_intertwines σ D hD g) x
  simp only [LinearMap.comp_apply] at h ⊢
  simp only [LinearEquiv.coe_coe]
  rw [LinearEquiv.apply_symm_apply]
  change coordinateActor σ D hD
      (TauCeti.Comodule.basePointsRepresentation (H := H) D.toRegularSubcomodule
        (TauCeti.AlgHom.mapDomain σ g) x) =
    TauCeti.Comodule.basePointsRepresentation (H := H) D.toRegularSubcomodule g
      (coordinateActor σ D hD x)
  exact h

end LinearActor

theorem coordinateBialgHom_surjective_of_generating_subcoalgebra
    {H : Type u} [CommRing H] [HopfAlgebra k H]
    (D : TauCeti.Subcoalgebra k H) (hgen : Algebra.adjoin k (D : Set H) = ⊤)
    {n : ℕ} (b : Module.Basis (Fin n) k D.toRegularSubcomodule) :
    Function.Surjective (TauCeti.Comodule.coordinateBialgHom (H := H) b) := by
  have hcoeff : TauCeti.Comodule.matrixCoefficientSubalgebra (R := k) (C := H)
      (M := D.toRegularSubcomodule) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact Algebra.adjoin_le fun x hx => D.le_matrixCoefficientSubalgebra_toRegularSubcomodule hx
  change Function.Surjective (TauCeti.Comodule.coordinateBialgHom (H := H) b).toAlgHom
  rw [← AlgHom.range_eq_top]
  apply top_unique
  rw [← hcoeff]
  exact TauCeti.Comodule.matrixCoefficientSubalgebra_le_coordinateBialgHom_range b

theorem exists_finite_invariant_generating_subcoalgebra_three
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : H →ₐc[k] H)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k H) :
    ∃ D : TauCeti.Subcoalgebra k H,
      Module.Finite k D.toSubmodule ∧ D.map σ.toCoalgHom = D ∧
        Algebra.adjoin k (D : Set H) = ⊤ := by
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k H).out
  obtain ⟨D, hD, hsD⟩ := TauCeti.Subcoalgebra.exists_finiteDimensional_subcoalgebra_of_setFinite
    (k := k) (C := H) (s : Set H) s.finite_toSet
  let : Module.Finite k D.toSubmodule := hD
  let E := cyclicClosureThree σ.toCoalgHom D
  have hc : (σ.toCoalgHom.comp σ.toCoalgHom).comp σ.toCoalgHom = CoalgHom.id k H :=
    congrArg BialgHom.toCoalgHom hσ
  refine ⟨E, finite_cyclicClosureThree _ _, map_cyclicClosureThree _ hc _, ?_⟩
  apply top_unique
  rw [← hs]
  apply Algebra.adjoin_mono
  intro x hx
  exact le_cyclicClosureThree σ.toCoalgHom D (hsD hx)

structure SemisimpleAffineCoordinatesThree
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : H →ₐc[k] H) where
  coalgebra : TauCeti.Subcoalgebra k H
  finite : Module.Finite k coalgebra.toSubmodule
  invariant : coalgebra.map σ.toCoalgHom = coalgebra
  generates : Algebra.adjoin k (coalgebra : Set H) = ⊤
  dimension : ℕ
  basis : Module.Basis (Fin dimension) k coalgebra.toRegularSubcomodule
  coordinateSurjective :
    Function.Surjective (TauCeti.Comodule.coordinateBialgHom (H := H) basis)
  actor : coalgebra.toRegularSubcomodule ≃ₗ[k] coalgebra.toRegularSubcomodule
  actor_cube : actor.toLinearMap ^ 3 = 1
  actor_semisimple :
    letI : AddCommGroup coalgebra.toRegularSubcomodule := Module.addCommMonoidToAddCommGroup k
    Module.End.IsSemisimple actor.toLinearMap
  actor_conj : ∀ g : WithConv (H →ₐ[k] k),
    TauCeti.Comodule.basePointsRepresentation (H := H) coalgebra.toRegularSubcomodule
        (TauCeti.AlgHom.mapDomain σ g) =
      actor.symm.toLinearMap ∘ₗ
        TauCeti.Comodule.basePointsRepresentation (H := H) coalgebra.toRegularSubcomodule g ∘ₗ
        actor.toLinearMap

theorem exists_semisimpleAffineCoordinatesThree
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (h3 : (3 : k) ≠ 0)
    (σ : H →ₐc[k] H) (hσ : (σ.comp σ).comp σ = BialgHom.id k H) :
    Nonempty (SemisimpleAffineCoordinatesThree H σ) := by
  obtain ⟨D, hD, hσD, hgen⟩ := exists_finite_invariant_generating_subcoalgebra_three H σ hσ
  let : Module.Finite k D.toSubmodule := hD
  let : Module.Finite k D.toRegularSubcomodule := D.toRegularSubcomodule_finite
  let : AddCommGroup D.toRegularSubcomodule := Module.addCommMonoidToAddCommGroup k
  let b := Module.finBasis k D.toRegularSubcomodule
  refine ⟨⟨D, hD, hσD, hgen, Module.finrank k D.toRegularSubcomodule, b,
    coordinateBialgHom_surjective_of_generating_subcoalgebra D hgen b,
    coordinateActorEquiv σ hσ D hσD, ?_, ?_, ?_⟩⟩
  · rw [coordinateActorEquiv_toLinearMap]
    exact coordinateActor_cube σ hσ D hσD
  · rw [coordinateActorEquiv_toLinearMap]
    exact coordinateActor_isSemisimple σ hσ D hσD h3
  · exact coordinateActor_conj σ hσ D hσD

namespace SemisimpleAffineCoordinatesThree

variable {H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k} {σ : H →ₐc[k] H}
variable (E : SemisimpleAffineCoordinatesThree H σ)

abbrev pointRepresentation :=
  TauCeti.Comodule.basePointsRepresentation (R := k) (H := H) E.coalgebra.toRegularSubcomodule

theorem pointRepresentation_injective : Function.Injective E.pointRepresentation :=
  basePointsRepresentation_injective_of_generating_subcoalgebra E.coalgebra E.generates

def conjugatingActor :
    LinearMap.GeneralLinearGroup k E.coalgebra.toRegularSubcomodule :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv E.actor.symm

local instance : AddCommGroup E.coalgebra.toRegularSubcomodule :=
  Module.addCommMonoidToAddCommGroup k

local instance : Module.Finite k E.coalgebra.toSubmodule := E.finite

local instance : Module.Finite k E.coalgebra.toRegularSubcomodule :=
  E.coalgebra.toRegularSubcomodule_finite

theorem conjugatingActor_cube : E.conjugatingActor ^ 3 = 1 := by
  have hi : LinearMap.GeneralLinearGroup.ofLinearEquiv E.actor.symm =
      (LinearMap.GeneralLinearGroup.ofLinearEquiv E.actor)⁻¹ :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv_inv E.actor
  rw [conjugatingActor, hi, inv_pow]
  have hu : (LinearMap.GeneralLinearGroup.ofLinearEquiv E.actor) ^ 3 = 1 := by
    apply Units.ext
    change E.actor.toLinearMap ^ 3 = 1
    exact E.actor_cube
  rw [hu, inv_one]

theorem pointRepresentation_mapDomain_eq_conj (g : WithConv (H →ₐ[k] k)) :
    E.pointRepresentation (TauCeti.AlgHom.mapDomain σ g) =
      (E.conjugatingActor : Module.End k E.coalgebra.toRegularSubcomodule) *
        E.pointRepresentation g *
        (((E.conjugatingActor)⁻¹ :
          LinearMap.GeneralLinearGroup k E.coalgebra.toRegularSubcomodule) :
          Module.End k E.coalgebra.toRegularSubcomodule) := by
  have heq (a : E.coalgebra.toRegularSubcomodule ≃ₗ[k] E.coalgebra.toRegularSubcomodule) :
      (LinearMap.GeneralLinearGroup.ofLinearEquiv a :
        Module.End k E.coalgebra.toRegularSubcomodule) = a.toLinearMap := by
    apply LinearMap.ext
    intro x
    exact congrFun (LinearMap.GeneralLinearGroup.coe_ofLinearEquiv a) x
  have hi : (LinearMap.GeneralLinearGroup.ofLinearEquiv E.actor.symm)⁻¹ =
      LinearMap.GeneralLinearGroup.ofLinearEquiv E.actor := by
    have hi' : (LinearMap.GeneralLinearGroup.ofLinearEquiv E.actor.symm)⁻¹ =
        LinearMap.GeneralLinearGroup.ofLinearEquiv E.actor.symm.symm :=
      (LinearMap.GeneralLinearGroup.ofLinearEquiv_inv E.actor.symm).symm
    simpa only [LinearEquiv.symm_symm] using hi'
  simpa only [pointRepresentation, conjugatingActor, hi, heq, Module.End.mul_eq_comp,
    LinearMap.comp_assoc] using E.actor_conj g

abbrev matrixRepresentation : WithConv (H →ₐ[k] k) →*
    Matrix.GeneralLinearGroup (Fin E.dimension) k :=
  (TauCeti.GeneralLinear.pointsMulEquiv E.dimension).toMonoidHom.comp
    (TauCeti.AlgHom.mapDomain (TauCeti.Comodule.coordinateBialgHom (H := H) E.basis))

def conjugatingMatrix : Matrix.GeneralLinearGroup (Fin E.dimension) k :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv E.basis).toMulEquiv E.conjugatingActor

theorem conjugatingMatrix_val :
    (E.conjugatingMatrix : Matrix (Fin E.dimension) (Fin E.dimension) k) =
      LinearMap.toMatrixAlgEquiv E.basis
        (E.conjugatingActor : Module.End k E.coalgebra.toRegularSubcomodule) := (rfl)

theorem conjugatingMatrix_cube : E.conjugatingMatrix ^ 3 = 1 := by
  have h := congrArg (Units.mapEquiv (LinearMap.toMatrixAlgEquiv E.basis).toMulEquiv)
    E.conjugatingActor_cube
  simpa only [map_pow, map_one, conjugatingMatrix] using h

theorem matrixRepresentation_injective : Function.Injective E.matrixRepresentation := by
  intro g h heq
  apply E.pointRepresentation_injective
  apply (LinearMap.toMatrixAlgEquiv E.basis).injective
  have hg := pointsMulEquiv_coordinateBialgHom_eq_toMatrix E.basis g
  have hh := pointsMulEquiv_coordinateBialgHom_eq_toMatrix E.basis h
  rw [← hg, ← hh]
  exact congrArg Units.val heq

theorem matrixRepresentation_mapDomain_eq_conj (g : WithConv (H →ₐ[k] k)) :
    E.matrixRepresentation (TauCeti.AlgHom.mapDomain σ g) =
      E.conjugatingMatrix * E.matrixRepresentation g * E.conjugatingMatrix⁻¹ := by
  apply Units.ext
  have hm (x : WithConv (H →ₐ[k] k)) :
      (E.matrixRepresentation x : Matrix (Fin E.dimension) (Fin E.dimension) k) =
        LinearMap.toMatrixAlgEquiv E.basis (E.pointRepresentation x) :=
    pointsMulEquiv_coordinateBialgHom_eq_toMatrix E.basis x
  have hmi : ((E.conjugatingMatrix⁻¹ :
      Matrix.GeneralLinearGroup (Fin E.dimension) k) :
      Matrix (Fin E.dimension) (Fin E.dimension) k) =
      LinearMap.toMatrixAlgEquiv E.basis
        (((E.conjugatingActor)⁻¹ :
          LinearMap.GeneralLinearGroup k E.coalgebra.toRegularSubcomodule) :
          Module.End k E.coalgebra.toRegularSubcomodule) := (rfl)
  have h := congrArg (LinearMap.toMatrixAlgEquiv E.basis)
    (E.pointRepresentation_mapDomain_eq_conj g)
  simpa only [hm, Units.val_mul, conjugatingMatrix_val, hmi, map_mul] using h

theorem mapDomain_cube (E : SemisimpleAffineCoordinatesThree H σ)
    (g : WithConv (H →ₐ[k] k)) :
    TauCeti.AlgHom.mapDomain σ (TauCeti.AlgHom.mapDomain σ
      (TauCeti.AlgHom.mapDomain σ g)) = g := by
  apply E.matrixRepresentation_injective
  calc
    E.matrixRepresentation (TauCeti.AlgHom.mapDomain σ (TauCeti.AlgHom.mapDomain σ
        (TauCeti.AlgHom.mapDomain σ g))) =
        E.conjugatingMatrix ^ 3 * E.matrixRepresentation g * (E.conjugatingMatrix ^ 3)⁻¹ := by
      rw [E.matrixRepresentation_mapDomain_eq_conj,
        E.matrixRepresentation_mapDomain_eq_conj, E.matrixRepresentation_mapDomain_eq_conj]
      simp only [pow_succ, pow_zero]
      group
    _ = E.matrixRepresentation g := by rw [E.conjugatingMatrix_cube]; simp

theorem coordinateEnd_cube [IsAlgClosed k] [IsReduced H]
    (E : SemisimpleAffineCoordinatesThree H σ) :
    (σ.comp σ).comp σ = BialgHom.id k H := by
  apply BialgHom.ext
  intro x
  simp only [BialgHom.comp_apply, BialgHom.id_apply]
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro g
  have h := congrArg (fun f : WithConv (H →ₐ[k] k) => f.ofConv x)
    (E.mapDomain_cube (WithConv.toConv g))
  simpa only [TauCeti.AlgHom.mapDomain_apply, WithConv.ofConv_toConv, AlgHom.comp_apply,
    BialgHom.comp_apply, BialgHom.coe_toAlgHom, BialgHom.id_apply] using h

end SemisimpleAffineCoordinatesThree

end CFSG.LieType.AlgebraicGroups
