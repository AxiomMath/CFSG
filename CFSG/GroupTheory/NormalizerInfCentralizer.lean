module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem mem_normalizer_inf_centralizer {L Q : Subgroup G} {c : G}
    (hcL : c ∈ Subgroup.normalizer (L : Set G))
    (hcQ : c ∈ Subgroup.normalizer (Q : Set G)) :
    c ∈ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hcQ, CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer L hcL⟩
