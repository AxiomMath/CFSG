module

public import CFSG.HardMathSupport.GuralnickMalle.CyclicTwoDecomp

@[expose] public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module
open scoped TensorProduct

section Jordan

variable {K : Type*} [Field K]

noncomputable def jordanDualBasis (n : ℕ) :
    Basis (Fin n) K (Module.Dual K (Fin n → K)) :=
  (Pi.basisFun K (Fin n)).dualBasis

noncomputable def jordanCyclicBasis (n : ℕ) :
    Basis (Fin n) K (Module.Dual K (Fin n → K)) :=
  (jordanDualBasis (K := K) n).reindex (Fin.revPerm (n := n))

end Jordan

section Contraction

variable {K : Type*} [Field K]

def linearMapEval {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (v : V) : (V →ₗ[K] W) →ₗ[K] W where
  toFun f := f v
  map_add' f g := rfl
  map_smul' a f := rfl

noncomputable def tensorContractionBilin (V W : Type*) [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] : V →ₗ[K] W →ₗ[K] (Module.Dual K V →ₗ[K] W) where
  toFun v :=
    { toFun := fun w =>
        { toFun := fun φ => φ v • w
          map_add' := fun φ ψ => by
            change (φ + ψ) v • w = φ v • w + ψ v • w
            rw [LinearMap.add_apply, add_smul]
          map_smul' := fun a φ => by
            change (a • φ) v • w = a • (φ v • w)
            rw [LinearMap.smul_apply]
            exact smul_assoc a (φ v) w }
      map_add' := fun w₁ w₂ => by
        apply LinearMap.ext
        intro φ
        change φ v • (w₁ + w₂) = φ v • w₁ + φ v • w₂
        rw [smul_add]
      map_smul' := fun a w => by
        apply LinearMap.ext
        intro φ
        change φ v • (a • w) = a • (φ v • w)
        exact smul_comm (φ v) a w }
  map_add' := fun v₁ v₂ => by
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro φ
    change (φ (v₁ + v₂)) • w = φ v₁ • w + φ v₂ • w
    rw [map_add, add_smul]
  map_smul' := fun a v => by
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro φ
    change (φ (a • v)) • w = a • (φ v • w)
    rw [map_smul]
    exact smul_assoc a (φ v) w

noncomputable def tensorContraction (V W : Type*) [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] : (V ⊗[K] W) →ₗ[K] (Module.Dual K V →ₗ[K] W) :=
  TensorProduct.lift (tensorContractionBilin (K := K) V W)

@[simp]
theorem tensorContraction_apply (V W : Type*) [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (t : V ⊗[K] W) :
    tensorContraction (K := K) V W t =
      TensorProduct.lift (tensorContractionBilin (K := K) V W) t := rfl

@[simp]
theorem tensorContraction_tmul {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (v : V) (w : W) (φ : Module.Dual K V) :
    tensorContraction (K := K) V W (v ⊗ₜ[K] w) φ = φ v • w := by
  rw [tensorContraction_apply, TensorProduct.lift.tmul]
  rfl

end Contraction

end CFSG.HardMathSupport.GuralnickMalle
