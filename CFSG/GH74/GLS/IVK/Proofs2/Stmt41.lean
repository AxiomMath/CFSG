module

public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

@[expose] def Lemma41dConclusion (p n : ℕ) {K : Type} [Group K] (P : Subgroup K) : Prop :=
  (∀ E : Subgroup K, E ≤ P → IsElementaryAbelian p ↥E →
      p ^ n ≤ (E.subgroupOf P).index ∧ Nat.card ↥E ≤ p ^ (2 * n)) ∧
    CFSG.Open.pCoreOf p (normalizer (((center ↥P).map P.subtype : Subgroup K) : Set K)) = P ∧
    center ↥P = ⁅(⊤ : Subgroup ↥P), (⊤ : Subgroup ↥P)⁆ ∧ center ↥P = frattini ↥P ∧
    IsElementaryAbelian p ↥(center ↥P) ∧ Nat.card ↥(center ↥P) = p ^ n

@[expose] def IVK_4_1d_L3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p n : ℕ), p.Prime → p ≠ 2 → IsLnEps 3 K 1 (p ^ n) →
    ∀ P : Sylow p K, Lemma41dConclusion p n (P : Subgroup K)

@[expose] def IVK_4_1d_U3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p n : ℕ), p.Prime → p ≠ 2 → IsLnEps 3 K (-1) (p ^ n) →
    ∀ P : Sylow p K, Lemma41dConclusion p n (P : Subgroup K)

@[expose] def IVK_4_1a_L3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p n : ℕ), p.Prime → p ≠ 2 → IsLnEps 3 K 1 (p ^ n) →
    ∀ z : K, orderOf z = 2 →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (N : Subgroup (GL (Fin 2) F)) (_ : N.Normal),
        Nat.card F = p ^ n ∧ (Nat.card ↥N = 1 ∨ Nat.card ↥N = 3) ∧
          Nonempty (↥(centralizer ({z} : Set K)) ≃* (GL (Fin 2) F ⧸ N))

end CFSG.GH74.GLS.IVK.Proofs2
