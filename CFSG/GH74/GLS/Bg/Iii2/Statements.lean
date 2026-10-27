module

public import CFSG.GH74.GLS.Bg.G4Statements
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Statements

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip

@[expose] def L41 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → 3 ≤ pRank 2 G →
    ∀ (x : G) (K : Subgroup G), IsTwoTerminal x K → pRank 2 ↥K = 1 →
      ∃ (x' : G) (K' : Subgroup G), IsRigidRankOneComp x' K'

@[expose] def PU : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → 3 ≤ pRank 2 G →
    ∀ (x u : G) (K : Subgroup G), IsRigidRankOneComp x K → orderOf u = 2 → u ∈ centralizer ({x} : Set G) →
      u ∈ cSec K → ∃ J : Subgroup G, IsRigidRankOneComp u J

@[expose] def CM : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → 3 ≤ pRank 2 G →
    ∀ (x u : G), orderOf x = 2 → orderOf u = 2 → u ∈ centralizer ({x} : Set G) →
      ∀ (R : Finset (Subgroup G)), (∀ K, K ∈ R ↔ IsRigidRankOneComp x K) →
        (∀ K ∈ R, u ∈ cSec K) →
        Set.ncard {J : Subgroup G | IsRigidRankOneComp u J} ≤ R.card →
        ∃ J : Subgroup G → Subgroup G, Set.InjOn J (R : Set (Subgroup G)) ∧
          (∀ K ∈ R, IsRigidRankOneComp u (J K)) ∧
          {J' : Subgroup G | IsRigidRankOneComp u J'} = J '' (R : Set (Subgroup G)) ∧
          ∀ K ∈ R, ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 P K →
            (∀ p ∈ P, u * p = p * u) → P ≤ J K

@[expose] def II4_43d : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (x : G), orderOf x = 2 →
    ∀ K : Subgroup G, IsRigidRankOneComp x K → ∀ u : G, u * u = 1 → u ∈ centralizer ({x} : Set G) →
      u ∈ normalizer (K : Set G) → ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 P K →
        (∀ p ∈ P, u * p = p * u) → u ∈ cSec K

structure ExtData (G : Type) [Group G] [Finite G] (x : G) (T : Subgroup G) : Prop where
  ord : orderOf x = 2
  nonempty : ∃ K : Subgroup G, IsRigidRankOneComp x K
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤
  le_cent : T ≤ centralizer ({x} : Set G)
  mem : x ∈ T
  mem_rigid : x ∈ rigidProduct x

@[expose] def ExtP : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → 3 ≤ pRank 2 G →
    (∃ (x : G) (K : Subgroup G), IsRigidRankOneComp x K) → ∃ (x : G) (T : Subgroup G), ExtData G x T

@[expose] def TailP : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → Gen4 G → 3 ≤ pRank 2 G →
    ∀ (x : G) (T : Subgroup G), ExtData G x T →
      ∃ t ∈ centralizer ({x} : Set G), IsConj x t ∧ t ∉ zStar (rigidProduct x)

theorem b_iii2_G4_of (hL41 : L41) (hExt : ExtP) (hTail : TailP) : B_iii2_G4 := by
  intro G _ _ hG hgen h3 x K hxK hK1
  obtain ⟨x₀, K₀, hK₀⟩ := hL41 G hG h3 x K hxK hK1
  obtain ⟨x₁, T, E⟩ := hExt G hG h3 ⟨x₀, K₀, hK₀⟩
  obtain ⟨K₁, hK₁⟩ := E.nonempty
  obtain ⟨t, ht, hconj, hnot⟩ := hTail G hG hgen h3 x₁ T E
  exact ⟨x₁, K₁, hK₁.1, hK₁.2, E.mem_rigid, t, ht, hconj, hnot⟩

end CFSG.GH74.GLS.Bg.Iii2
