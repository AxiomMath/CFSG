module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Thm3.Sec5

@[expose] def ActsAsPerm {G : Type} [Group G] (t : G) (K : Subgroup G) (n : ℕ)
    (e : (HatT K ⧸ center (HatT K)) ≃* alternatingGroup (Fin n)) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k : ↥K, ∃ k' : ↥K, (k' : G) = t * (k : G) * t⁻¹ ∧
    ((e (QuotientGroup.mk (QuotientGroup.mk k')) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
      σ * ((e (QuotientGroup.mk (QuotientGroup.mk k)) : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)) * σ⁻¹

@[expose] def Lemma9_6Outer3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh] (z t : G) (S K : Subgroup G),
    Std9 G Lh z t S K → RigidSet Lh z = {K} → Qof S K = zpowers z →
      ∀ n : ℕ, (n = 8 ∨ n = 9) → IsDoubleCoverOfAlt Lh n →
        ∀ (e : (HatT K ⧸ center (HatT K)) ≃* alternatingGroup (Fin n)) (σ : Equiv.Perm (Fin n)),
          σ.cycleType = {2, 2, 2} → ActsAsPerm t K n e σ → False

end CFSG.GH74.GLS.Stage1.Thm4
