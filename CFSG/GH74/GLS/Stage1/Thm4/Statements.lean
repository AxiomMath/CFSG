module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

@[expose] def Prop9_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh], Hyp9 G Lh →
    ∃ (z t : G) (K : Subgroup G), Good92 G Lh z t K

@[expose] def Lemma9_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh] (z t : G) (S K : Subgroup G),
    Std9 G Lh z t S K → ∀ n : ℕ, IsDoubleCoverOfAlt Lh n →
      ∀ K' ∈ RigidSet Lh z, ∃ k : ↥K', t * (k : G)⁻¹ ∈ cSec K' ∧
        IsFourTransp (HatT K') n (QuotientGroup.mk k)

@[expose] def Lemma9_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh] (z t : G) (S K : Subgroup G),
    Std9 G Lh z t S K → RigidSet Lh z = {K}

@[expose] def Step9_8_Q1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh] (z t : G) (S K : Subgroup G),
    Std9 G Lh z t S K → RigidSet Lh z = {K} → Qof S K = zpowers z

@[expose] def Lemma9_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh] (z t : G) (S K : Subgroup G),
    Std9 G Lh z t S K → RigidSet Lh z = {K} →
      ∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Stage1Sporadic G z S n ∧ IsCentralInvolution z

@[expose] def Prop9_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh] (z t : G) (S K : Subgroup G),
    Std9 G Lh z t S K →
      RigidSet Lh z = {K} ∧
      ∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Stage1Sporadic G z S n ∧ IsCentralInvolution z

end CFSG.GH74.GLS.Stage1.Thm4
