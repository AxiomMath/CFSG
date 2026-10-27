module

public import CFSG.ClassicalInvolution.ModelFacts.MF15Defs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.MF15

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

structure LinData (Q : QuadraticForm F V) where
  x : SemiSim Q
  hφ : ∀ c, x.φ c = c
  s : F
  hs : ∀ v, x.toFun (x.toFun v) = s • v

namespace LinData

variable (d : LinData Q)

theorem smul (c : F) (v : V) : d.x.toFun (c • v) = c • d.x.toFun v := by
  rw [d.x.map_smul', d.hφ]

@[expose] def lin : V →ₗ[F] V where
  toFun := d.x.toFun
  map_add' := d.x.map_add'
  map_smul' c v := by rw [d.smul, RingHom.id_apply]

@[simp] theorem lin_apply (v : V) : d.lin v = d.x.toFun v := rfl

end LinData

end CFSG.ClassicalInvolution.ModelFacts.MF15
