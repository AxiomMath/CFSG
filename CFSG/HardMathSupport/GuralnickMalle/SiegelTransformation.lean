module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic

public section

open LinearMap Module

namespace CFSG.HardMathSupport.GuralnickMalle

variable {K E : Type*} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]

section Counterexample

abbrev ExSpace (K : Type*) := (K × K) × (K × K)

variable (K : Type*) [Field K] [CharP K 2]

@[expose] def exTau : ExSpace K ≃ₗ[K] ExSpace K := LinearEquiv.prodComm K (K × K) (K × K)

@[simp] theorem exTau_apply (x : ExSpace K) : exTau K x = (x.2, x.1) := rfl

@[expose] def exDiag : (K × K) →ₗ[K] ExSpace K := LinearMap.prod LinearMap.id LinearMap.id

@[simp] theorem exDiag_apply (u : K × K) : exDiag K u = (u, u) := rfl

end Counterexample

section LongRootGroup

noncomputable def siegelLin (Qf : QuadraticForm K E) (a b : E) (c : K) : E →ₗ[K] E :=
  LinearMap.id + (c • (QuadraticMap.polarBilin Qf).flip b).smulRight a +
    (c • (QuadraticMap.polarBilin Qf).flip a).smulRight b

theorem siegelLin_apply (Qf : QuadraticForm K E) (a b : E) (c : K) (x : E) :
    siegelLin Qf a b c x = x + c • (QuadraticMap.polarBilin Qf x b • a) +
      c • (QuadraticMap.polarBilin Qf x a • b) := by
  simp only [siegelLin, LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, LinearMap.id_apply, BilinForm.flip_apply,
    QuadraticMap.polarBilin_apply_apply, smul_smul]
  abel

@[simp] theorem siegelLin_zero (Qf : QuadraticForm K E) (a b : E) :
    siegelLin Qf a b 0 = LinearMap.id := by
  ext x
  simp only [siegelLin_apply, zero_smul, add_zero, LinearMap.id_apply]

end LongRootGroup

end CFSG.HardMathSupport.GuralnickMalle
