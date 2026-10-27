module

public import CFSG.GH74.GLS.Bg.Pu5.Statements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip

structure Cfg295 (G : Type) [Group G] [Finite G] (z t : G) (S K U : Subgroup G) : Prop where
  cfg : Cfg G z t S
  hK : IsRigidRankOneComp z K
  hU : IsFour U
  hUle : U ≤ centralizer ({z, t} : Set G) ⊓ cSec K
  hzU : z ∈ U
  hzi : ∀ y ∈ S ⊓ K, orderOf y = 2 → y ∈ U

@[expose] def P0S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G) (S K U : Subgroup G), Cfg295 G z t S K U →
    ∀ u ∈ U, orderOf u = 2 → z ∈ zStar (rigidProduct u)

@[expose] def L295aS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G) (S K U : Subgroup G), Cfg295 G z t S K U →
    ∀ L : Subgroup G, IsRigidRankOneComp t L → U ≤ normalizer (L : Set G)

@[expose] def L295bS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G) (S K U : Subgroup G), Cfg295 G z t S K U →
    (∀ L : Subgroup G, IsRigidRankOneComp t L → U ≤ normalizer (L : Set G)) →
      ∀ L : Subgroup G, IsRigidRankOneComp t L → ∀ u ∈ U, orderOf u = 2 → ¬ InducesFAut u L

@[expose] def L295cS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z t : G) (S K U : Subgroup G), Cfg295 G z t S K U →
    (∀ L : Subgroup G, IsRigidRankOneComp t L → U ≤ normalizer (L : Set G)) →
      (∀ L : Subgroup G, IsRigidRankOneComp t L → ∀ u ∈ U, orderOf u = 2 → ¬ InducesFAut u L) →
        ∀ L : Subgroup G, IsRigidRankOneComp t L → ∀ u ∈ U, u ∉ zpowers z → ¬ InducesInner u L

theorem l295_of_parts (ha : L295aS) (hb : L295bS) (hc : L295cS) : L295 := by
  intro G _ _ z t S hC K hK U hU hUle hzU hzi
  have hcfg : Cfg295 G z t S K U := ⟨hC, hK, hU, hUle, hzU, hzi⟩
  have ha' := ha G z t S K U hcfg
  have hb' := hb G z t S K U hcfg ha'
  exact ⟨ha', hb', hc G z t S K U hcfg ha' hb'⟩

end CFSG.GH74.GLS.Bg.Pu5
