module

public import CFSG.LieType.AlgebraicGroups.ClosedOrbitFixed
public import TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra

public noncomputable section

open WithConv TauCeti.Comodule
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]

section Tensor

attribute [local instance] TauCeti.Comodule.tensor

variable {M E : Type u} [AddCommGroup M] [Module k M] [TauCeti.Comodule k H M]
  [AddCommGroup E] [Module k E] [TauCeti.Comodule k H E]

end Tensor

section Exterior

attribute [local instance] TauCeti.Comodule.exteriorAlgebra

variable {M : Type u} [AddCommGroup M] [Module k M] [TauCeti.Comodule k H M]

theorem basePointsRepresentation_exteriorAlgebra_ι (x : WithConv (H →ₐ[k] k)) (m : M) :
    basePointsRepresentation (H := H) (ExteriorAlgebra k M) x (ExteriorAlgebra.ι k m) =
      ExteriorAlgebra.ι k (basePointsRepresentation (H := H) M x m) := by
  simpa using (basePointsRepresentation_comm_hom (Hom.exteriorAlgebraι k H M) x m).symm

theorem basePointsRepresentation_exteriorAlgebra_one (x : WithConv (H →ₐ[k] k)) :
    basePointsRepresentation (H := H) (ExteriorAlgebra k M) x 1 = 1 := by
  rw [basePointsRepresentation_apply, ← Algebra.TensorProduct.one_def,
    endOfPoint_exteriorAlgebra_one, Algebra.TensorProduct.one_def, TensorProduct.lid_tmul,
    one_smul]

theorem basePointsRepresentation_exteriorAlgebra_mul (x : WithConv (H →ₐ[k] k))
    (a b : ExteriorAlgebra k M) :
    basePointsRepresentation (H := H) (ExteriorAlgebra k M) x (a * b) =
      basePointsRepresentation (H := H) (ExteriorAlgebra k M) x a *
        basePointsRepresentation (H := H) (ExteriorAlgebra k M) x b := by
  rw [basePointsRepresentation_apply, basePointsRepresentation_apply,
    basePointsRepresentation_apply,
    show (1 : k) ⊗ₜ[k] (a * b) = ((1 : k) ⊗ₜ[k] a) * ((1 : k) ⊗ₜ[k] b) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
    endOfPoint_exteriorAlgebra_mul, ← Algebra.TensorProduct.lid_toLinearEquiv]
  exact map_mul (Algebra.TensorProduct.lid k (ExteriorAlgebra k M)) _ _

@[expose] def basePointsExteriorAlgHom (x : WithConv (H →ₐ[k] k)) :
    ExteriorAlgebra k M →ₐ[k] ExteriorAlgebra k M :=
  AlgHom.ofLinearMap (basePointsRepresentation (H := H) (ExteriorAlgebra k M) x)
    (basePointsRepresentation_exteriorAlgebra_one x) (basePointsRepresentation_exteriorAlgebra_mul x)

theorem basePointsExteriorAlgHom_apply (x : WithConv (H →ₐ[k] k)) (w : ExteriorAlgebra k M) :
    basePointsExteriorAlgHom (H := H) x w =
      basePointsRepresentation (H := H) (ExteriorAlgebra k M) x w :=
  rfl

theorem exteriorAlgebraMap_basePointsRepresentation_of_lift
    {τ : WithConv (H →ₐ[k] k) → WithConv (H →ₐ[k] k)} {F : M →ₗ[k] M}
    (hF : ∀ x v, F (basePointsRepresentation (H := H) M x v) =
      basePointsRepresentation (H := H) M (τ x) (F v))
    (x : WithConv (H →ₐ[k] k)) (w : ExteriorAlgebra k M) :
    ExteriorAlgebra.map F (basePointsRepresentation (H := H) (ExteriorAlgebra k M) x w) =
      basePointsRepresentation (H := H) (ExteriorAlgebra k M) (τ x) (ExteriorAlgebra.map F w) := by
  have h : (ExteriorAlgebra.map F).comp (basePointsExteriorAlgHom (H := H) x) =
      (basePointsExteriorAlgHom (H := H) (τ x)).comp (ExteriorAlgebra.map F) := by
    apply ExteriorAlgebra.hom_ext
    ext m
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.comp_apply, basePointsExteriorAlgHom_apply, basePointsRepresentation_exteriorAlgebra_ι,
      ExteriorAlgebra.map_apply_ι, hF]
  exact AlgHom.congr_fun h w

end Exterior

section Regular

@[expose] def restrictSubcomodule (V : TauCeti.Subcomodule k H H) (φ : H →ₐc[k] H)
    (hφV : ∀ v ∈ V, φ v ∈ V) : V →ₗ[k] V where
  toFun v := ⟨φ v, hφV v v.2⟩
  map_add' v w := Subtype.ext (by simp)
  map_smul' c v := Subtype.ext (by simp)

@[simp]
theorem coe_restrictSubcomodule (V : TauCeti.Subcomodule k H H) (φ : H →ₐc[k] H)
    (hφV : ∀ v ∈ V, φ v ∈ V) (v : V) :
    (restrictSubcomodule V φ hφV v : H) = φ v :=
  rfl

@[expose] def restrictSubcomoduleEquiv (V : TauCeti.Subcomodule k H H) (φ ψ : H →ₐc[k] H)
    (hψφ : (ψ : H →ₐ[k] H).comp (φ : H →ₐ[k] H) = AlgHom.id k H)
    (hφψ : (φ : H →ₐ[k] H).comp (ψ : H →ₐ[k] H) = AlgHom.id k H)
    (hφV : ∀ v ∈ V, φ v ∈ V) (hψV : ∀ v ∈ V, ψ v ∈ V) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinear (restrictSubcomodule V φ hφV) (restrictSubcomodule V ψ hψV)
    (LinearMap.ext fun v => Subtype.ext (AlgHom.congr_fun hφψ v))
    (LinearMap.ext fun v => Subtype.ext (AlgHom.congr_fun hψφ v))

@[simp]
theorem coe_restrictSubcomoduleEquiv (V : TauCeti.Subcomodule k H H) (φ ψ : H →ₐc[k] H)
    (hψφ : (ψ : H →ₐ[k] H).comp (φ : H →ₐ[k] H) = AlgHom.id k H)
    (hφψ : (φ : H →ₐ[k] H).comp (ψ : H →ₐ[k] H) = AlgHom.id k H)
    (hφV : ∀ v ∈ V, φ v ∈ V) (hψV : ∀ v ∈ V, ψ v ∈ V) (v : V) :
    (restrictSubcomoduleEquiv V φ ψ hψφ hφψ hφV hψV v : H) = φ v :=
  rfl

end Regular

end CFSG.LieType.AlgebraicGroups.ClosedCone
