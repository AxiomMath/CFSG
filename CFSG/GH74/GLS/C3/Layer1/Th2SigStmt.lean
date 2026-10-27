module

public import CFSG.GH74.GLS.C3.Layer1.Th2Defs

public section

namespace CFSG.GH74.GLS

open Subgroup

@[expose] def B_IG_21_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (k : ℕ), 1 ≤ k → ∀ A B : Subgroup G,
    IsE (k + 2) ⊤ A → IsKBal k A → IsE (k + 1) A B → thetaK k B = thetaK k A

@[expose] def B_IG_21_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (k : ℕ), 1 ≤ k → ∀ A B : Subgroup G,
    IsE (k + 2) ⊤ A → IsKBal (k + 1) A → IsWeakKBal k A → IsE (k + 1) A B →
      thetaHalf k B = thetaHalf k A

@[expose] def B_IG_21_6_half : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G),
    IsE 4 ⊤ A → IsKBal 3 A → IsWeakKBal 2 A → Odd (Nat.card ↥(thetaHalf 2 A))

end CFSG.GH74.GLS
