module

public import CFSG.GH74.GLS.Stage12.Interface

public section

namespace CFSG.GH74.GLS.Bg

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank

@[expose] def B_pu5_G4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → Gen4 G → 3 ≤ pRank 2 G → ∀ z : G,
    orderOf z = 2 → z ∈ rigidProduct z → IsStronglyClassicalInvolution G z

@[expose] def B_iii2_G4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → Gen4 G → 3 ≤ pRank 2 G →
    ∀ (x : G) (K : Subgroup G), IsTwoTerminal x K → pRank 2 ↥K = 1 →
      ∃ (x' : G) (K' : Subgroup G), IsPRigid 2 x' K' ∧ pRank 2 ↥K' = 1 ∧ x' ∈ rigidProduct x' ∧
        ∃ t ∈ centralizer ({x'} : Set G), IsConj x' t ∧ t ∉ zStar (rigidProduct x')

end CFSG.GH74.GLS.Bg

namespace CFSG.GH74.GLS.Stage1.Thm2

open CFSG.GH74.GLS

theorem s_stage1_thm2_Std_of_G4 (hpu5 : Bg.B_pu5_G4) (hiii2 : Bg.B_iii2_G4) : Stage12.S_stage1_thm2_Std := by
  intro G _ _ hStd ⟨x, K, hxK, hK1⟩
  obtain ⟨x', K', hrig, hK'1, hx', t, ht, hconj, hnot⟩ :=
    hiii2 G hStd.kps hStd.gen4 hStd.rank.1 x K hxK hK1
  exact ⟨x', hpu5 G hStd.kps hStd.gen4 hStd.rank.1 x' hrig.1.1 hx', t, ht, hconj, hnot⟩

end CFSG.GH74.GLS.Stage1.Thm2
