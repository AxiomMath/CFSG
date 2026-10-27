module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.GH74.GLS.IVK.Defs2

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK
open scoped Matrix

@[expose] def GU2Stated (q : ℕ) (F : Type) [Field F] : Subgroup (GL (Fin 2) F) :=
  Subgroup.closure {A | ((A : Matrix (Fin 2) (Fin 2) F).map (· ^ q))ᵀ * (A : Matrix (Fin 2) (Fin 2) F) = 1}

@[expose] def IVK_4_1a_U3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p n : ℕ), p.Prime → p ≠ 2 → IsLnEps 3 K (-1) (p ^ n) →
    ∀ z : K, orderOf z = 2 →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (N : Subgroup ↥(GU2Stated (p ^ n) F))
        (_ : N.Normal), Nat.card F = (p ^ n) ^ 2 ∧ (Nat.card ↥N = 1 ∨ Nat.card ↥N = 3) ∧
          Nonempty (↥(centralizer ({z} : Set K)) ≃* (↥(GU2Stated (p ^ n) F) ⧸ N))

end CFSG.GH74.GLS.IVK.Proofs2
