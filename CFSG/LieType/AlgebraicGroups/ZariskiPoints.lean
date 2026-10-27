module

public import CFSG.LieType.AlgebraicGroups.PointSurjectivityExtension
public import Mathlib.RingTheory.Spectrum.Prime.Topology

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TensorProduct Topology

variable {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A]

@[expose] def pointSpec (y : A →ₐ[k] k) : PrimeSpectrum A :=
  ⟨RingHom.ker y, RingHom.ker_isPrime y⟩

theorem pointSpec_asIdeal (y : A →ₐ[k] k) : (pointSpec y).asIdeal = RingHom.ker y :=
  rfl

theorem pointSpec_injective : Function.Injective (pointSpec (k := k) (A := A)) := by
  intro y y' h
  have h' : RingHom.ker y = RingHom.ker y' := congrArg PrimeSpectrum.asIdeal h
  ext a
  have hmem : a - algebraMap k A (y a) ∈ RingHom.ker y := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  rw [h', RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero] at hmem
  exact hmem.symm

theorem comap_pointSpec {B : Type} [CommRing B] [Algebra k B] (φ : B →ₐ[k] A) (y : A →ₐ[k] k) :
    PrimeSpectrum.comap (φ : B →+* A) (pointSpec y) = pointSpec (y.comp φ) :=
  rfl

variable (k) in
@[expose] def IsPointConstructible (S : Set (A →ₐ[k] k)) : Prop :=
  ∃ C : Set (PrimeSpectrum A), IsConstructible C ∧ S = pointSpec ⁻¹' C

variable (k) in
@[expose] def IsPointClosed (S : Set (A →ₐ[k] k)) : Prop :=
  ∃ Z : Set (PrimeSpectrum A), IsClosed Z ∧ S = pointSpec ⁻¹' Z

variable (k) in
@[expose] def IsPointIrreducible (S : Set (A →ₐ[k] k)) : Prop :=
  IsIrreducible (pointSpec '' S)

theorem exists_comp_eq_iff_mem_range_comap [IsAlgClosed k] {D : Type} [CommRing D] [Algebra k D]
    [Algebra.FiniteType k D] (φ : A →ₐ[k] D) (y : A →ₐ[k] k) :
    (∃ z : D →ₐ[k] k, z.comp φ = y) ↔
      pointSpec y ∈ Set.range (PrimeSpectrum.comap (φ : A →+* D)) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨pointSpec z, rfl⟩
  · intro h
    let : Algebra A D := (φ : A →+* D).toAlgebra
    have : IsScalarTower k A D := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    obtain ⟨z, hz⟩ := exists_algHom_of_mem_range_comap y h
    exact ⟨z, AlgHom.ext fun a => congrArg (fun g : A →ₐ[k] k => g a) hz⟩

theorem isPointConstructible_iUnion_range [IsAlgClosed k] [Algebra.FiniteType k A] {J : Type}
    [Finite J] (D : J → Type) [∀ j, CommRing (D j)] [∀ j, Algebra k (D j)]
    [∀ j, Algebra.FiniteType k (D j)] (φ : ∀ j, A →ₐ[k] D j) :
    IsPointConstructible k (⋃ j, Set.range fun z : D j →ₐ[k] k => z.comp (φ j)) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hfp : ∀ j, (φ j : A →+* D j).FinitePresentation := fun j => by
    refine RingHom.FinitePresentation.of_finiteType.1 ?_
    refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap k A) ?_
    rw [(φ j).comp_algebraMap]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  refine ⟨⋃ j, Set.range (PrimeSpectrum.comap (φ j : A →+* D j)),
    IsConstructible.iUnion fun j => PrimeSpectrum.isConstructible_range_comap (hfp j), ?_⟩
  ext y
  simp only [Set.mem_iUnion, Set.mem_preimage]
  exact exists_congr fun j => exists_comp_eq_iff_mem_range_comap (φ j) y

theorem isPointIrreducible_range_of_isDomain [IsAlgClosed k] {D : Type} [CommRing D]
    [Algebra k D] [Algebra.FiniteType k D] [IsDomain D] (φ : A →ₐ[k] D) :
    IsPointIrreducible k (Set.range fun z : D →ₐ[k] k => z.comp φ) := by
  have : IsJacobsonRing D := isJacobsonRing_of_finiteType (A := k)
  have hcl : closedPoints (PrimeSpectrum D) = Set.range (pointSpec (k := k) (A := D)) := by
    ext p
    constructor
    · intro hp
      have : p.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).1 hp
      obtain ⟨z, hz⟩ := exists_algHom_ker_eq k D p.asIdeal
      exact ⟨z, PrimeSpectrum.ext hz⟩
    · rintro ⟨z, rfl⟩
      refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 ?_
      exact RingHom.ker_isMaximal_of_surjective _ fun c => ⟨algebraMap k D c, z.commutes c⟩
  have hirr : IsIrreducible (closedPoints (PrimeSpectrum D)) := by
    rw [← isIrreducible_iff_closure, closure_closedPoints]
    exact IrreducibleSpace.isIrreducible_univ _
  have h := hirr.image (PrimeSpectrum.comap (φ : A →+* D))
    (PrimeSpectrum.continuous_comap _).continuousOn
  rw [hcl, ← Set.range_comp] at h
  unfold IsPointIrreducible
  rw [← Set.range_comp]
  exact h

theorem isPointIrreducible_iUnion_of_directed {ι : Type} [Nonempty ι] (S : ι → Set (A →ₐ[k] k))
    (hS : ∀ i, IsPointIrreducible k (S i)) (hdir : ∀ i j, ∃ l, S i ⊆ S l ∧ S j ⊆ S l) :
    IsPointIrreducible k (⋃ i, S i) := by
  unfold IsPointIrreducible at hS ⊢
  rw [Set.image_iUnion]
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨?_, fun u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩ => ?_⟩
  · obtain ⟨p, hp⟩ := (hS i₀).nonempty
    exact ⟨p, Set.mem_iUnion.2 ⟨i₀, hp⟩⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hb
    obtain ⟨l, hil, hjl⟩ := hdir i j
    obtain ⟨c, hc, hcuv⟩ := (hS l).2 u v hu hv ⟨a, Set.image_mono hil hi, hau⟩
      ⟨b, Set.image_mono hjl hj, hbv⟩
    exact ⟨c, Set.mem_iUnion.2 ⟨l, hc⟩, hcuv⟩

variable {B : Type} [CommRing B] [Algebra k B]

@[expose] def tensorPointEquiv : (A →ₐ[k] k) × (B →ₐ[k] k) ≃ (A ⊗[k] B →ₐ[k] k) where
  toFun p := Algebra.TensorProduct.productMap p.1 p.2
  invFun y := (y.comp Algebra.TensorProduct.includeLeft, y.comp Algebra.TensorProduct.includeRight)
  left_inv p := by
    ext a <;> simp
  right_inv y := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [← map_mul]

theorem tensorPointEquiv_tmul (p : (A →ₐ[k] k) × (B →ₐ[k] k)) (a : A) (b : B) :
    tensorPointEquiv p (a ⊗ₜ b) = p.1 a * p.2 b := by
  simp [tensorPointEquiv]

end CFSG.LieType.AlgebraicGroups
