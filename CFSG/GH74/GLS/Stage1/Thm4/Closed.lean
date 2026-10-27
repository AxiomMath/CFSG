module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

structure Hyp5B (H : Type) [Group H] [Finite H] (K : Subgroup H) (n : ℕ) : Prop where
  normal : K.Normal
  n_ge : 8 ≤ n
  n_le : n ≤ 11
  cover : IsDoubleCoverOfAlt ↥K n
  cent : ∀ h : H, (∀ k ∈ K, h * k = k * h) → h ∈ K

@[expose] def IVK_5_1_index : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (K : Subgroup H) (n : ℕ), Hyp5B H K n → K.index ≤ 2

@[expose] def IVK_5_1g : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (K : Subgroup H) (n : ℕ), Hyp5B H K n →
    ∀ T : Subgroup H, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → ∀ w ∈ T, (∀ s ∈ T, s * w = w * s) →
      w ∈ K ∧ ∀ k ∈ K, k * w = w * k

@[expose] def IVK_5_1f : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n : ℕ), IsDoubleCoverOfAlt K n → 8 ≤ n → n ≤ 11 →
    ∀ u v : K, orderOf u = 2 → orderOf v = 2 → u ∉ center K → v ∉ center K → IsConj u v

@[expose] def IVK_5_1d : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (K : Subgroup H) (n : ℕ), Hyp5B H K n → K.index = 2 →
    ∃ h : H, h ∉ K ∧ orderOf h = 2

@[expose] def Step9_8_Fstar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh] (z t : G) (S K : Subgroup G),
    Std9 G Lh z t S K → RigidSet Lh z = {K} → Qof S K = zpowers z →
      ∀ c ∈ Cz z, (∀ k ∈ K, ⁅k, c⁆ ∈ Oz z) → c ∈ zpowers z ⊔ Oz z

@[expose] def Step9_8_inv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh] (z t : G) (S K : Subgroup G),
    Std9 G Lh z t S K → RigidSet Lh z = {K} → Qof S K = zpowers z →
      ∀ u ∈ S, orderOf u = 2 → IsConj z u → u ∈ K

end CFSG.GH74.GLS.Stage1.Thm4
