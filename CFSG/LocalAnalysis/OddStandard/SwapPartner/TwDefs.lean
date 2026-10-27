module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm CFSG.Blueprint

theorem swap_mul_swap_mem_alternatingGroup :
    (swap 0 1 * swap 2 3 : Perm (Fin 8)) ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  rfl

@[expose] def abType22 : alternatingGroup (Fin 8) :=
  ⟨swap 0 1 * swap 2 3, swap_mul_swap_mem_alternatingGroup⟩

theorem abType22_ne_one : abType22 ≠ 1 := by
  intro h
  have h' : (swap 0 1 * swap 2 3 : Perm (Fin 8)) = 1 := congrArg Subtype.val h
  have h'' := congrArg (fun p : Perm (Fin 8) => p 0) h'
  revert h''
  decide

@[expose] def TwHSFusion : Prop :=
  ∀ (N : Type) [Group N] [Finite N], Nonempty (N ≃* NativeSporadic.HS) →
    ∀ τ : MulAut N, τ * τ = 1 →
    ∀ (B : Subgroup N) (eB : B ≃* alternatingGroup (Fin 8)), (∀ b : B, τ (b : N) = b) →
    ∀ g : MulAut N, g * τ * g⁻¹ ≠ τ * MulAut.conj ((eB.symm abType22 : B) : N)

end CFSG.OddStandard.AltStdSec.SwapPartner
