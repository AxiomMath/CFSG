module

public import CFSG.LieType.AlgebraicGroups.FullFlagCone
public import CFSG.LieType.AlgebraicGroups.ChevalleyLine

public noncomputable section

open WithConv TauCeti.Comodule
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u

variable {k H V : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable [AddCommGroup V] [Module k V] [TauCeti.Comodule k H V]

attribute [local instance] TauCeti.Comodule.exteriorAlgebra TauCeti.Comodule.tensor

@[expose] def exteriorPowerData (r : ℕ) :
    Σ c : TauCeti.Comodule k H (⋀[k]^r V),
      letI := c
      {f : TauCeti.Comodule.Hom k H (⋀[k]^r V) (ExteriorAlgebra k V) //
        f.toLinearMap = (⋀[k]^r V).subtype} := by
  rw [← exteriorPowerSubcomodule_toSubmodule (R := k) (H := H) (M := V) r]
  exact ⟨TauCeti.Subcomodule.instComodule (N := exteriorPowerSubcomodule k H V r),
    ⟨(exteriorPowerSubcomodule k H V r).subtype, by
      rw [TauCeti.Subcomodule.subtype_toLinearMap]
      ext p
      change (p : ExteriorAlgebra k V) = (p : ExteriorAlgebra k V)
      rfl⟩⟩

@[expose, instance_reducible] def exteriorPowerComodule (r : ℕ) :
    TauCeti.Comodule k H (⋀[k]^r V) :=
  (exteriorPowerData (H := H) (V := V) r).1

attribute [local instance] exteriorPowerComodule

@[expose] def exteriorPowerSubtype (r : ℕ) :
    TauCeti.Comodule.Hom k H (⋀[k]^r V) (ExteriorAlgebra k V) :=
  (exteriorPowerData (H := H) (V := V) r).2.val

theorem exteriorPowerSubtype_toLinearMap (r : ℕ) :
    (exteriorPowerSubtype (H := H) (V := V) r).toLinearMap = (⋀[k]^r V).subtype :=
  (exteriorPowerData (H := H) (V := V) r).2.property

instance flagTensorComodule : (r : ℕ) → TauCeti.Comodule k H (FlagTensor k V r)
  | 0 => TauCeti.Comodule.trivial
  | r + 1 => by
    letI := flagTensorComodule r
    exact inferInstanceAs (TauCeti.Comodule k H
      (FlagTensor k V r ⊗[k] (⋀[k]^(r + 1) V)))

theorem basePointsRepresentation_exteriorPower_coe (r : ℕ)
    (g : WithConv (H →ₐ[k] k)) (p : ⋀[k]^r V) :
    (basePointsRepresentation (H := H) (⋀[k]^r V) g p : ExteriorAlgebra k V) =
      basePointsRepresentation (H := H) (ExteriorAlgebra k V) g (p : ExteriorAlgebra k V) := by
  simpa only [exteriorPowerSubtype_toLinearMap, Submodule.subtype_apply] using
    basePointsRepresentation_comm_hom (exteriorPowerSubtype (H := H) (V := V) r) g p

theorem basePointsRepresentation_exteriorPower (r : ℕ)
    (g : WithConv (H →ₐ[k] k)) (p : ⋀[k]^r V) :
    basePointsRepresentation (H := H) (⋀[k]^r V) g p =
      exteriorPower.map r (basePointsRepresentation (H := H) V g) p := by
  apply Subtype.ext
  rw [basePointsRepresentation_exteriorPower_coe, exteriorPower.coe_map,
    basePointsRepresentation_exteriorAlgebra_eq_map]

theorem basePointsRepresentation_flag (r : ℕ) (g : WithConv (H →ₐ[k] k))
    (z : FlagTensor k V r) :
    basePointsRepresentation (H := H) (FlagTensor k V r) g z =
      flagMap (basePointsRepresentation (H := H) V g) r z := by
  induction r with
  | zero =>
    let : TauCeti.Comodule k H (FlagTensor k V 0) := flagTensorComodule (H := H) (V := V) 0
    exact basePointsRepresentation_eq_of_coact_eq_tmul_one z rfl g
  | succ r ih =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul w p =>
      rw [basePointsRepresentation_tmul, flagMap_tmul, ih, basePointsRepresentation_exteriorPower]
    | add z z' hz hz' => simp only [map_add, hz, hz']

theorem basePointsRepresentation_mem_flagCone {d : ℕ} (b : Module.Basis (Fin d) k V)
    (r : ℕ) (g : WithConv (H →ₐ[k] k)) {z : FlagTensor k V r} (hz : z ∈ flagCone b r) :
    basePointsRepresentation (H := H) (FlagTensor k V r) g z ∈ flagCone b r := by
  let e : V ≃ₗ[k] V := LinearMap.GeneralLinearGroup.generalLinearEquiv k V
    (Representation.asGroupHom (basePointsRepresentation (R := k) (H := H) V) g)
  have he : e.toLinearMap = basePointsRepresentation (H := H) V g := by
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv k V
      (Representation.asGroupHom (basePointsRepresentation (R := k) (H := H) V) g) :
        V →ₗ[k] V) = _
    rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
      Representation.asGroupHom_apply]
  rw [basePointsRepresentation_flag]
  have h := flagMap_mem_flagCone b e r hz
  rwa [he] at h

theorem exists_isZariskiClosed_orbitCone_flag [IsAlgClosed k] [Algebra.FiniteType k H]
    [IsDomain H] [FiniteDimensional k V] :
    ∃ w ∈ flagCone (Module.finBasis k V) (Module.finrank k V), w ≠ 0 ∧
      IsZariskiClosed k (orbitCone k H w) := by
  apply exists_isZariskiClosed_orbitCone
    (isZariskiClosed_flagCone (Module.finBasis k V) _) (isCone_flagCone (Module.finBasis k V) _)
  · exact fun g _ hz => basePointsRepresentation_mem_flagCone (Module.finBasis k V) _ g hz
  · exact exists_ne_zero_mem_flagCone

end CFSG.LieType.AlgebraicGroups.ClosedCone
