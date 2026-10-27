module

public import CFSG.GH74.Uniqueness.SU.KInputs2

public section

namespace CFSG.GH74.Uniqueness.SU.K

open Subgroup CFSG.Blueprint

@[expose] def KI8c : Prop :=
  ∀ (H : Type) [Group H] [Finite H], pPrimeCore 2 H = ⊥ → OneInvClass H →
    ∀ (T : Sylow 2 H) (z : H), z ∈ (T : Subgroup H) → orderOf z = 2 →
      (∀ t ∈ (T : Subgroup H), t * z = z * t) →
      Nonempty (CBar H z ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
        Open.IsElemAbelian 3 (OC H z) →
          (OC H z = ⊥ ∧ (Nonempty (H ≃* alternatingGroup (Fin 4)) ∨ LieModel H .PSL 2 5 1)) ∨
          (Nat.card (OC H z) = 3 ∧ (LieModel H .PSL 2 11 1 ∨ LieModel H .PSL 2 13 1))

end CFSG.GH74.Uniqueness.SU.K
