module

public import CFSG.LieType.AlgebraicGroups.ClosedOrbitCone
public import CFSG.LieType.AlgebraicGroups.ConeFixedPoint
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FiniteType
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Solvable

public noncomputable section

open WithConv TauCeti.Comodule

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u v w

variable {k : Type u} [Field k] [IsAlgClosed k] {H : Type v} [CommRing H] [HopfAlgebra k H]
variable [Algebra.FiniteType k H]

theorem hasNonzeroWeightVector_of_forall_mem_span [IsReduced H]
    {M : Type w} [AddCommGroup M] [Module k M] [TauCeti.Comodule k H M] [FiniteDimensional k M]
    {v : M} (hv : v ≠ 0)
    (h : ∀ g : WithConv (H →ₐ[k] k), basePointsRepresentation (H := H) M g v ∈ k ∙ v) :
    HasNonzeroWeightVector k H M := by
  refine TauCeti.Comodule.hasNonzeroWeightVector_of_basePointsRepresentation_stable
    (k := k) (H := H) (M := M) (k ∙ v) v hv rfl ?_
  intro g m hm
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
  simpa only [map_smul] using Submodule.smul_mem (k ∙ v) c (h g)

theorem isSolvable_of_forall_isZariskiClosed_orbitCone [IsDomain H]
    (h : ∀ (W : Type v) [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W]
      [FiniteDimensional k W] (w : W), w ≠ 0 → IsZariskiClosed k (orbitCone k H w) →
        ∀ g : WithConv (H →ₐ[k] k), basePointsRepresentation (H := H) W g w ∈ k ∙ w) :
    Group.IsSolvable (WithConv (H →ₐ[k] k)) := by
  classical
  have hweight : ∀ (W : Type v) [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W]
      [FiniteDimensional k W] [Nontrivial W], HasNonzeroWeightVector k H W := by
    intro W _ _ _ _ _
    have hC : IsZariskiClosed k (Set.univ : Set W) := ⟨∅, by ext v; simp [zeroSet]⟩
    have hcone : IsCone k (Set.univ : Set W) := fun c v _ => Set.mem_univ _
    have hG : ∀ g : WithConv (H →ₐ[k] k), ∀ v ∈ (Set.univ : Set W),
        basePointsRepresentation (H := H) W g v ∈ (Set.univ : Set W) :=
      fun g v _ => Set.mem_univ _
    have hne : ∃ v ∈ (Set.univ : Set W), v ≠ 0 := by
      obtain ⟨w, hw⟩ := exists_ne (0 : W)
      exact ⟨w, Set.mem_univ _, hw⟩
    obtain ⟨w, -, hw0, hcl⟩ := exists_isZariskiClosed_orbitCone (k := k) (H := H)
      (M := W) (C := Set.univ) hC hcone hG hne
    exact hasNonzeroWeightVector_of_forall_mem_span (k := k) (H := H) (M := W) hw0
      (h W w hw0 hcl)
  obtain ⟨E, hEfin, hEtop⟩ :=
    TauCeti.Comodule.exists_finite_subcomodule_matrixCoefficientSubalgebra_eq_top
      (k := k) (C := H)
  let _ : Module.Finite k E := hEfin
  let _ : AddCommGroup E := Module.addCommMonoidToAddCommGroup k
  obtain ⟨n, b, htri, _hdiag⟩ :=
    TauCeti.Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_weight_vectors
      (k := k) (C := H) (M := E) hweight
  let ρ : WithConv (H →ₐ[k] k) →* GL (Fin n) k :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom).comp
      (basePointsRepresentation (H := H) E).toHomUnits
  have hρupper : ∀ g : WithConv (H →ₐ[k] k),
      ρ g ∈ TauCeti.upperTriangularGroup (Fin n) k := by
    intro g
    rw [TauCeti.UpperTriangularGroup.mem_iff]
    intro i j hji
    rw [show ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
        (LinearMap.toMatrix b b (basePointsRepresentation (H := H) E g)) i j by
      simp [ρ, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]]
    rw [LinearMap.toMatrix_apply]
    change b.coord i (basePointsRepresentation (H := H) E g (b j)) = 0
    rw [coord_basePointsRepresentation]
    exact Finset.sum_eq_zero fun l _ => by
      by_cases hlj : l = j
      · subst hlj
        rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_pos rfl, one_mul,
          htri hji, map_zero]
      · rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply,
          if_neg (Ne.symm hlj), zero_mul]
  have hrep : Function.Injective (basePointsRepresentation (R := k) (H := H) E) := by
    intro g g' hgg
    apply WithConv.ofConv_injective
    refine AlgHom.ext_of_adjoin_eq_top
      (s := matrixCoefficientSet (R := k) (C := H) (M := E)) ?_ ?_
    · rw [← matrixCoefficientSubalgebra_def]
      exact hEtop
    · intro c hc
      obtain ⟨φ, e, rfl⟩ := (mem_matrixCoefficientSet_iff (R := k) (C := H) (M := E) c).mp hc
      rw [apply_matrixCoefficient, apply_matrixCoefficient]
      exact congrArg φ (DFunLike.congr_fun hgg e)
  have hρinj : Function.Injective ρ := by
    intro g g' hgg
    apply hrep
    have hM : (LinearMap.toMatrixAlgEquiv b)
        (((basePointsRepresentation (R := k) (H := H) E).toHomUnits g :
          (Module.End k E)ˣ) : Module.End k E) =
        (LinearMap.toMatrixAlgEquiv b)
          (((basePointsRepresentation (R := k) (H := H) E).toHomUnits g' :
            (Module.End k E)ˣ) : Module.End k E) := by
      have hx := congrArg (fun x : GL (Fin n) k => (x : Matrix (Fin n) (Fin n) k)) hgg
      change (LinearMap.toMatrixAlgEquiv b)
          (((basePointsRepresentation (R := k) (H := H) E).toHomUnits g :
            (Module.End k E)ˣ) : Module.End k E) =
        (LinearMap.toMatrixAlgEquiv b)
          (((basePointsRepresentation (R := k) (H := H) E).toHomUnits g' :
            (Module.End k E)ˣ) : Module.End k E) at hx
      exact hx
    have h1 := (LinearMap.toMatrixAlgEquiv b).injective hM
    simpa only [MonoidHom.coe_toHomUnits] using h1
  let ρ' : WithConv (H →ₐ[k] k) →* TauCeti.upperTriangularGroup (Fin n) k :=
    ρ.codRestrict (TauCeti.upperTriangularGroup (Fin n) k) hρupper
  have hρ'inj : Function.Injective ρ' := by
    intro g g' hgg
    apply hρinj
    have h := congrArg (fun x : TauCeti.upperTriangularGroup (Fin n) k =>
      (x : GL (Fin n) k)) hgg
    simpa only [ρ', MonoidHom.codRestrict_apply, Subgroup.coe_mk] using h
  exact Group.isSolvable_of_isSolvable_injective hρ'inj

end CFSG.LieType.AlgebraicGroups.ClosedCone
