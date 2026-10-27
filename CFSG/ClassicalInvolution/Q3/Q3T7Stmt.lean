module

public import CFSG.ClassicalInvolution.Q3.Q3DStand

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Disc3

section Stmt


structure Std7Three {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop where
  stand : AscStand3 Ω K
  disconnected : ¬ DConnected Ω
  hz : IsUniqueInvolution K z
  hK' : K' ∈ twinSet Ω K
  hne : K' ≠ K
  cex : ¬ ConcOrTF4 G
  rank : 3 ≤ CFSG.Open.twoRank G

@[expose] def Hyp23Three {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' : Subgroup G) (z : G) : Prop :=
  Std7Three Ω K K' z ∧ KPerp Ω K = {K, K'}

@[expose] def WzThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand3 Ω K → ∀ z : G, IsUniqueInvolution K z → ∃ W ∈ WSet Ω, z ∈ W

@[expose] def C21_2Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Std7Three Ω K K' z → KPerp Ω K = twinSet Ω K

@[expose] def C22_1Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Std7Three Ω K K' z → KPerp Ω K = twinSet Ω K →
      KPerp Ω K = {K, K'} ∨ ConcOrTF4 G

@[expose] def C23_1Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23Three Ω K K' z → ∀ W ∈ WSet Ω, MuIsoE4 Ω W ∨ MuIsoS4 Ω W

@[expose] def C23_3Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23Three Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoS4 Ω W →
      W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥ ∨ ConcOrTF4 G

@[expose] def C24_1Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23Three Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoS4 Ω W →
      W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥ → ConcOrTF4 G

@[expose] def C25_E4Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23Three Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoE4 Ω W → ConcOrTF4 G

structure Thm7Steps3 : Prop where
  wz : WzThree
  s21 : C21_2Three
  s22 : C22_1Three
  s231 : C23_1Three
  s233 : C23_3Three
  s24 : C24_1Three
  s25 : C25_E4Three

end Stmt

end CFSG.ClassicalInvolution.Q3.Q3T7
