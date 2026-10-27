module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Models
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFlagKernel
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

@[expose] noncomputable def dualCoord : Module.Dual (ZMod 2) Vec3 ≃ₗ[ZMod 2] Vec3 :=
  (Pi.basisFun (ZMod 2) (Fin 3)).dualBasis.equivFun

theorem dualCoord_apply (f : Module.Dual (ZMod 2) Vec3) (i : Fin 3) :
    dualCoord f i = f (Pi.single i 1) := by
  simp [dualCoord, Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr]

theorem dual_apply_eq_sum (f : Module.Dual (ZMod 2) Vec3) (v : Vec3) :
    f v = ∑ j, v j * f (Pi.single j 1) := by
  have := LinearMap.pi_apply_eq_sum_univ f v
  have h : ∀ x : Fin 3, (fun j : Fin 3 => if x = j then (1 : ZMod 2) else 0) = Pi.single x 1 := by
    intro x
    funext j
    simp [Pi.single_apply, eq_comm]
  simpa only [h, smul_eq_mul] using this

theorem repV_symm (g : GL32) : (repV g).symm = repV g⁻¹ := rfl

theorem dualCoord_dualAct (g : GL32) (f : Module.Dual (ZMod 2) Vec3) :
    dualCoord (dualAct (repV g) f) = repDual g (dualCoord f) := by
  funext i
  rw [dualCoord_apply]
  change f ((repV g).symm (Pi.single i 1)) = _
  rw [repV_symm, repV_apply, dual_apply_eq_sum f, repDual_apply]
  simp only [dualCoord_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem actIso_dualAct_repDual : ActIso (fun (g : GL32) (f : Module.Dual (ZMod 2) Vec3) =>
    dualAct (repV g) f) (fun g x => repDual g x) :=
  ⟨dualCoord, fun g f => dualCoord_dualAct g f⟩

theorem isIrrAct_dualAct : IsIrrAct (fun (g : GL32) (f : Module.Dual (ZMod 2) Vec3) =>
    dualAct (repV g) f) :=
  IsIrrAct.of_actIso actIso_dualAct_repDual.symm isIrr_repDual

theorem actIso_repV_bidual : ActIso (fun (g : GL32) (v : Vec3) => repV g v)
    (fun g (φ : Module.Dual (ZMod 2) (Module.Dual (ZMod 2) Vec3)) =>
      dualAct ((repV g).symm.dualMap) φ) := by
  refine ⟨Module.evalEquiv (ZMod 2) Vec3, fun g v => ?_⟩
  ext f
  simp [dualAct, LinearEquiv.dualMap_symm]

theorem isIrrAct_bidual : IsIrrAct (fun (g : GL32)
    (φ : Module.Dual (ZMod 2) (Module.Dual (ZMod 2) Vec3)) => dualAct ((repV g).symm.dualMap) φ) :=
  IsIrrAct.of_actIso actIso_repV_bidual isIrr_repV

@[expose] noncomputable def actA (g : GL32) (X : traceZeroEnd Vec3) : traceZeroEnd Vec3 :=
  ⟨(repV g).conj (X : Module.End (ZMod 2) Vec3), by
    show LinearMap.trace (ZMod 2) Vec3 _ = 0
    rw [LinearMap.trace_conj']
    exact X.2⟩

theorem actA_coe (g : GL32) (X : traceZeroEnd Vec3) :
    (actA g X : Module.End (ZMod 2) Vec3) =
      (repV g : Vec3 →ₗ[ZMod 2] Vec3) ∘ₗ (X : Module.End (ZMod 2) Vec3) ∘ₗ
        ((repV g).symm : Vec3 →ₗ[ZMod 2] Vec3) :=
  (LinearEquiv.conj_apply _ _).trans (LinearMap.comp_assoc _ _ _)

theorem toMatrix'_repV (g : GL32) :
    LinearMap.toMatrix' (repV g : Vec3 →ₗ[ZMod 2] Vec3) = (g : Mat3) := by
  have : (repV g : Vec3 →ₗ[ZMod 2] Vec3) = Matrix.toLin' (g : Mat3) := LinearMap.ext fun v => rfl
  rw [this, LinearMap.toMatrix'_toLin']

theorem map_toMatrix'_traceZeroEnd :
    (traceZeroEnd Vec3).map
      (LinearMap.toMatrix' : Module.End (ZMod 2) Vec3 ≃ₗ[ZMod 2] Mat3).toLinearMap = traceZero := by
  ext M
  have key : ∀ X : Module.End (ZMod 2) Vec3,
      LinearMap.trace (ZMod 2) Vec3 X = Matrix.trace (LinearMap.toMatrix' X) := fun X => by
    rw [LinearMap.trace_eq_matrix_trace (ZMod 2) (Pi.basisFun (ZMod 2) (Fin 3)) X,
      LinearMap.toMatrix_eq_toMatrix']
  constructor
  · rintro ⟨X, hX, rfl⟩
    have h1 : LinearMap.trace (ZMod 2) Vec3 X = 0 := hX
    rw [key] at h1
    exact h1
  · intro hM
    refine ⟨LinearMap.toMatrix'.symm M, ?_, LinearMap.toMatrix'.apply_symm_apply M⟩
    show LinearMap.trace (ZMod 2) Vec3 _ = 0
    rw [key, LinearEquiv.apply_symm_apply]
    exact hM

@[expose] noncomputable def matEnd : traceZeroEnd Vec3 ≃ₗ[ZMod 2] traceZero :=
  (LinearMap.toMatrix' : Module.End (ZMod 2) Vec3 ≃ₗ[ZMod 2] Mat3).ofSubmodules
    (traceZeroEnd Vec3) traceZero map_toMatrix'_traceZeroEnd

theorem actIso_actA_repA : ActIso actA (fun g x => repA g x) := by
  refine ⟨matEnd, fun g X => ?_⟩
  apply Subtype.ext
  change LinearMap.toMatrix' ((repV g).conj (X : Module.End (ZMod 2) Vec3)) =
    (g : Mat3) * LinearMap.toMatrix' (X : Module.End (ZMod 2) Vec3) * ((g⁻¹ : GL32) : Mat3)
  rw [LinearEquiv.conj_apply, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, repV_symm,
    toMatrix'_repV, toMatrix'_repV]

theorem isIrrAct_actA : IsIrrAct actA :=
  IsIrrAct.of_actIso actIso_actA_repA.symm isIrr_repA

end CFSG.QuasithinUnique.Setup.Family
