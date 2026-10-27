module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SStd

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected

section Twins


structure Std7A7 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop where
  stand : Std2A7 Ω K
  disconnected : ¬ DConnected Ω
  hz : IsUniqueInvolution K z
  hK' : K' ∈ twinSet Ω K
  hne : K' ≠ K

@[expose] def A7C21_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Std7A7 Ω K K' z → KPerp Ω K = twinSet Ω K

@[expose] def A7C22_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Std7A7 Ω K K' z → KPerp Ω K = twinSet Ω K → KPerp Ω K = {K, K'}

@[expose] def Hyp23A7 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop :=
  Std7A7 Ω K K' z ∧ KPerp Ω K = {K, K'}

@[expose] def A7C23_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23A7 Ω K K' z → ∀ W ∈ WSet Ω, MuIsoE4 Ω W ∨ MuIsoS4 Ω W

@[expose] def A7C23_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23A7 Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoS4 Ω W →
      W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥

@[expose] def A7C24_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23A7 Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoS4 Ω W →
      W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥ → False

@[expose] def A7C25_E4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23A7 Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoE4 Ω W → False

@[expose] def A7Wz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    Std2A7 Ω K → ∀ z : G, IsUniqueInvolution K z → ∃ W ∈ WSet Ω, z ∈ W

theorem a7T7_of_steps (hWz : A7Wz) (h21 : A7C21_2) (h22 : A7C22_1) (h231 : A7C23_1)
    (h233 : A7C23_3) (h24 : A7C24_1) (h25 : A7C25_E4) : A7T7 := by
  intro G _ _ _ Ω K hs ⟨K', hK'tw, hK'ne⟩ hdisc
  obtain ⟨⟨z, hU⟩, -⟩ := hs.hyp.omega1 K hs.mem
  have hstd : Std7A7 Ω K K' z := ⟨hs, hdisc, hU, hK'tw, hK'ne⟩
  have hperp : KPerp Ω K = twinSet Ω K := h21 G Ω K K' z hstd
  have hyp23 : Hyp23A7 Ω K K' z := ⟨hstd, h22 G Ω K K' z hstd hperp⟩
  obtain ⟨W, hW, hzW⟩ := hWz G Ω K hs z hU
  rcases h231 G Ω K K' z hyp23 W hW with hE4 | hS4
  · exact h25 G Ω K K' z hyp23 W hW hzW hE4
  · exact h24 G Ω K K' z hyp23 W hW hzW hS4 (h233 G Ω K K' z hyp23 W hW hzW hS4)

end Twins

end CFSG.ClassicalInvolution.Hat2A7S
