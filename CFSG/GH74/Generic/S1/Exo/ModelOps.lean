module

public import CFSG.GH74.Generic.S1.BlkSplit

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup
open scoped MatrixGroups

variable {F : Type} [Field F]

structure ModelOps (S : Subgroup (GL (Fin 4) F)) where
  ops : BlockOps F S
  pf : PairFacts ops
  blkq : ∀ a b : Fin 4, a ≠ b → IsQuasisimple ↥(ops.blk a b)
  qM : ℕ
  qM_odd : Odd qM
  blk_model : ∀ a b : Fin 4, a ≠ b → ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀),
    Nat.card F₀ = qM ∧ Nonempty (SL(2, F₀) ≃* ↥(ops.blk a b))
  z0 : ↥S
  z0_mem : z0 ∈ ops.blk 0 1
  z0_sq : z0 * z0 = 1
  z0_ne : z0 ≠ 1
  z0_cent : ∀ g ∈ ops.blk 0 1, g * z0 = z0 * g
  neg : ↥S
  neg_center : ∀ g : ↥S, g ∈ Subgroup.center ↥S ↔ g = 1 ∨ g = neg
  neg_sq : neg * neg = 1
  neg_ne : neg ≠ 1
  norm : ∀ s : ↥S, s * s = 1 → s ≠ 1 → s ≠ neg → ∃ P : ↥S, P * s * P⁻¹ = z0
  swap : ∃ h : ↥S, h * z0 * h⁻¹ = neg * z0

namespace ModelOps

variable {S : Subgroup (GL (Fin 4) F)} (mo : ModelOps S)

theorem neg_mem_center : mo.neg ∈ Subgroup.center ↥S := (mo.neg_center mo.neg).2 (Or.inr rfl)

end ModelOps

end CFSG.GH74.Generic.S1.Exo
