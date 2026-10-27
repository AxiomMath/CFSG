module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Sp4Two
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Sp4TwoRootSix

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem factZ3RootSp4Two (hK : Nat.card K = 2) : FactZ3RootSp4Two K :=
  fun _ hy => exists_isSpRootSL2_mem_of_orderOf_eq_three hK hy

section B2

theorem not_normal_map_oddCore_nonsplit_of_card_eq_two {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .F4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ₀ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hX₀ : Nat.card X₀ = 3)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal :=
  not_normal_map_oddCore_nonsplit_two_of_sp4Z3 hset hK e ht hKt (factZ3RootSp4Two hK) hXJ₀ hX₀
    hX hDe

end B2

end CFSG.SeitzReduction.F4Pilot
