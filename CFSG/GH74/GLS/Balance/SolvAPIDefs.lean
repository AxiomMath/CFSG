module

public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

structure SolvAPI (x : X) (V : Subgroup X) where
  P : Subgroup X
  w : X
  hVC : V ≤ centralizer ({x} : Set X)
  V_subnormal : (V.subgroupOf (centralizer ({x} : Set X))).IsSubnormal
  O_le_V : pPrimeCoreOf 2 (centralizer ({x} : Set X)) ≤ V
  gen : ∀ H : Subgroup X, (∀ v ∈ V, Nat.Coprime (orderOf v) 2 → v ∈ H) → V ≤ H
  P_le : P ≤ V
  P_two : IsPGroup 2 P
  P_sylow : ∀ T : Subgroup X, T ≤ V → IsPGroup 2 T → Nat.card T ≤ Nat.card P
  P_nonab : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a
  w_mem : w ∈ V
  w_three : ∃ k : ℕ, orderOf w = 3 ^ k
  w_norm : w ∈ normalizer (P : Set X)
  P_comm : ⁅P, zpowers w⁆ = P
  w3 : ∀ a ∈ P, w ^ 3 * a = a * w ^ 3
  P_le_R : P ≤ oPrimeResidualOf 2 V
  R_gen : ∀ K : Subgroup X, oPrimeResidualOf 2 V ≤ normalizer (K : Set X) → P ≤ K →
    oPrimeResidualOf 2 V ≤ K
  T_le : ∀ T : Subgroup X, T ≤ centralizer ({x} : Set X) → IsPGroup 2 T →
    w ∈ normalizer (T : Set X) → ⁅T, zpowers w⁆ = T → T ≠ ⊥ →
      T ≤ V ∧ Nat.card T = Nat.card P ∧ ∃ a ∈ T, ∃ b ∈ T, a * b ≠ b * a
  abelian : orderOf x = 2 → ∀ T : Subgroup X, IsPGroup 2 T → (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) →
    w ∈ normalizer (T : Set X) → x ∈ normalizer (T : Set X) → ⁅T, zpowers w⁆ = ⊥
  dich : ∀ N : Subgroup X, IsPGroup 2 N → N ≤ centralizer ({x} : Set X) →
    centralizer ({x} : Set X) ≤ normalizer (N : Set X) →
      oPrimeResidualOf 2 V ≤ N ∨ V ≤ centralizer (N : Set X)
  central_mod : ∀ N : Subgroup X, V ≤ normalizer (N : Set X) → ¬ oPrimeResidualOf 2 V ≤ N →
    ∀ g ∈ N ⊓ V, ∀ v ∈ V, ⁅g, v⁆ ∈ pPrimeCoreOf 2 (centralizer ({x} : Set X))
  R_le_pPrimePCore : oPrimeResidualOf 2 V ≤
    (pPrimePCore 2 ↥(centralizer ({x} : Set X))).map (centralizer ({x} : Set X)).subtype

end CFSG.GH74.GLS.Balance
