module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.RepresentationTheory.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ExtendScalars
public import CFSG.GH74.GLS.Stage4.T2SL2Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped TensorProduct MonoidAlgebra

section Model

variable (F L : Type) [Field F] [Field L]

abbrev SLm (F : Type) [Field F] : Type := Matrix.SpecialLinearGroup (Fin 2) F

@[expose] noncomputable def funRep : Representation L (SLm F) ((Fin 2 → F) → L) where
  toFun g :=
    { toFun := fun f v => f (((g⁻¹ : SLm F) : Matrix (Fin 2) (Fin 2) F).mulVec v)
      map_add' := fun f f' => rfl
      map_smul' := fun c f => rfl }
  map_one' := by
    ext f v
    simp
  map_mul' := by
    intro g h
    ext f v
    show f ((((g * h)⁻¹ : SLm F) : Matrix (Fin 2) (Fin 2) F).mulVec v) =
      f ((((h⁻¹ : SLm F)) : Matrix (Fin 2) (Fin 2) F).mulVec
        ((((g⁻¹ : SLm F)) : Matrix (Fin 2) (Fin 2) F).mulVec v))
    rw [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]

variable [Algebra F L]

@[expose] noncomputable def monoFun (i j : ℕ) : (Fin 2 → F) → L :=
  fun v => (algebraMap F L (v 0)) ^ i * (algebraMap F L (v 1)) ^ j

@[expose] noncomputable def steinbergSub (A : ℕ) : Submodule L ((Fin 2 → F) → L) :=
  Submodule.span L (Set.range fun g : SLm F => funRep F L g (monoFun F L A 0))

theorem steinbergSub_stable (A : ℕ) (g : SLm F) {f : (Fin 2 → F) → L}
    (hf : f ∈ steinbergSub F L A) : funRep F L g f ∈ steinbergSub F L A := by
  unfold steinbergSub at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    refine Submodule.subset_span ⟨g * h, ?_⟩
    simp [map_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

@[expose] noncomputable def steinbergRep (A : ℕ) : Representation L (SLm F) ↥(steinbergSub F L A) where
  toFun g := (funRep F L g).restrict (fun f hf => steinbergSub_stable F L A g hf)
  map_one' := by
    ext f v
    simp
  map_mul' := by
    intro g h
    ext f v
    simp

end Model

section Digits

@[expose] def rot (p n A : ℕ) : ℕ := (A % p ^ (n - 1)) * p + A / p ^ (n - 1)

@[expose] def digitProd (p n A : ℕ) : ℕ := ∏ i ∈ Finset.range n, (A / p ^ i % p + 1)

@[expose] noncomputable def rotPeriod (p n A : ℕ) : ℕ := Function.minimalPeriod (rot p n) A

end Digits

section Constituent

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Finite F]

@[expose] def HasConstituent {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Algebra (ZMod p) F]
    (σ : Representation (ZMod p) (SLm F) W) (A : ℕ) : Prop :=
  ∃ f : (steinbergRep F F A).asModule →ₗ[MonoidAlgebra F (SLm F)]
      (CFSG.Theory.Representation.extendScalars F σ).asModule, f ≠ 0

end Constituent

end CFSG.GH74.GLS.Stage4.Rest
