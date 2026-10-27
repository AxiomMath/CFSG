module

public import CFSG.GH74.E2.Cl2Defs

public section

namespace CFSG.GH74.E2

open Subgroup

abbrev dsub (Q : Type*) [Group Q] : Subgroup Q := ⁅(⊤ : Subgroup Q), ⊤⁆

structure Cl3 (Q : Type*) [Group Q] (a b : MulAut Q) (N : Subgroup Q) : Prop where
  bpair : BPair Q a b
  four : FourGen Q
  N_central : N ≤ center Q
  N_elem : ∀ n ∈ N, n * n = 1
  N_ne : N ≠ ⊥
  N_inva : ∀ n ∈ N, a n ∈ N
  N_invb : ∀ n ∈ N, b n ∈ N
  N_eq : N = ⁅dsub Q, ⊤⁆
  N_simple : ∀ M : Subgroup Q, M ≤ N → (∀ x ∈ M, a x ∈ M) → (∀ x ∈ M, b x ∈ M) →
    M = ⊥ ∨ M = N

end CFSG.GH74.E2
