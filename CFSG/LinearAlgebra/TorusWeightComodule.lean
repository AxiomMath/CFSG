module

public import CFSG.Mathlib.RingTheory.RootsOfUnity.ZModUnits
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Weight
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic
public import Mathlib.Tactic.Continuity.Init
public import Mathlib.Topology.Sheaves.Init
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction

public noncomputable section

namespace CFSG.LinearAlgebra

open Matrix Module TauCeti WithConv
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {r : ℕ}
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
variable [Comodule k (MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) V]

theorem exists_basis_mem_torusWeightSpace :
    ∃ (ι : Type u) (_ : Fintype ι) (b : Basis ι k V)
      (wt : ι → Multiplicative (Fin r →₀ ℤ)),
      ∀ i, b i ∈ Comodule.weightSpace k (Multiplicative (Fin r →₀ ℤ)) V (wt i) := by
  let : DecidableEq (Multiplicative (Fin r →₀ ℤ)) := Classical.decEq _
  let : DecidableEq V := Classical.decEq _
  let W := Comodule.weightSpace k (Multiplicative (Fin r →₀ ℤ)) V
  let α := fun m : Multiplicative (Fin r →₀ ℤ) => ↥(Basis.ofVectorSpaceIndex k (W m))
  let b' := fun m : Multiplicative (Fin r →₀ ℤ) => Basis.ofVectorSpace k (W m)
  let b : Basis (Σ m, α m) k V :=
    (Comodule.isInternal_weightSpace k (Multiplicative (Fin r →₀ ℤ)) V).collectedBasis b'
  let : Fintype (Σ m, α m) := FiniteDimensional.fintypeBasisIndex b
  exact ⟨_, inferInstance, b, fun i => i.1,
    (Comodule.isInternal_weightSpace k (Multiplicative (Fin r →₀ ℤ)) V).collectedBasis_mem b'⟩

omit [Module.Finite k V] in
theorem basePointsRepresentation_of_mem_torusWeightSpace
    {μ : Fin r → ℤ} {v : V}
    (hv : v ∈ Comodule.weightSpace k (Multiplicative (Fin r →₀ ℤ)) V (SplitTorus.weightCharacter μ))
    (s : Fin r → kˣ) : Comodule.basePointsRepresentation
      (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) V
      (SplitTorus.pointsMulEquiv.symm s) v = (torusCharacter s μ : k) • v := by
  rw [Comodule.basePointsRepresentation_apply,
    Comodule.endOfPoint_tmul_of_mem_weightSpace _ 1 hv]
  simp only [one_mul, TensorProduct.lid_tmul]
  have h := congrArg Units.val (SplitTorus.charOfPoint_weightCharacter
    ((SplitTorus.pointsMulEquiv (R := k) (A := k) (σ := Fin r)).symm s) μ)
  rw [MulEquiv.apply_symm_apply, DiagonalizableGroup.charOfPoint_apply_coe] at h
  rw [h]

omit [Module.Finite k V] in
theorem basisWeightTorus_eq_basePointsRepresentation_of_mem
    {ι : Type u} [Fintype ι] (b : Basis ι k V) (wt : ι → Fin r → ℤ)
    (hb : ∀ i, b i ∈ Comodule.weightSpace k (Multiplicative (Fin r →₀ ℤ)) V
      (SplitTorus.weightCharacter (wt i))) (s : Fin r → kˣ) :
    (basisWeightTorus b wt s).toLinearMap = Comodule.basePointsRepresentation
      (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) V
      (SplitTorus.pointsMulEquiv.symm s) := by
  apply b.ext
  intro i
  change basisWeightTorus b wt s (b i) = _
  rw [basisWeightTorus_basis, basePointsRepresentation_of_mem_torusWeightSpace (hb i)]

theorem exists_basisWeightTorus_eq_basePointsRepresentation :
    ∃ (ι : Type u) (_ : Fintype ι) (b : Basis ι k V) (wt : ι → Fin r → ℤ),
      ∀ (s : Fin r → kˣ) (v : V),
        basisWeightTorus b wt s v = Comodule.basePointsRepresentation
          (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) V
          (SplitTorus.pointsMulEquiv.symm s) v := by
  obtain ⟨ι, hι, b, wt, hb⟩ := exists_basis_mem_torusWeightSpace (k := k) (r := r) (V := V)
  let : Fintype ι := hι
  let wt' : ι → Fin r → ℤ := fun i => (wt i).toAdd
  have hwt (i : ι) : SplitTorus.weightCharacter (wt' i) = wt i := by
    apply Multiplicative.ext
    ext j
    simp [wt']
  refine ⟨ι, inferInstance, b, wt', fun s v => ?_⟩
  exact congrArg (fun f : V →ₗ[k] V => f v)
    (basisWeightTorus_eq_basePointsRepresentation_of_mem b wt'
      (fun i => by rw [hwt]; exact hb i) s)

end CFSG.LinearAlgebra
