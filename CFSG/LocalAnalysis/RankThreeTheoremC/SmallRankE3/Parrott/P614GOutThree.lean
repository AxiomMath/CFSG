module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GOut
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GLieThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {M B H S K : Subgroup G} {z : G}

theorem false_of_not_cyclic_three (c : Ctx M B H S K z) (hR0 : kRad H S K = pCoreOf 2 H)
    (hKD : CFSG.LieType.ChevTwo.Chev2KDOut) (hTwo : KFactTwoInvolutionsThree)
    (hOut : CFSG.LieType.ChevTwo.Chev2OutTwoRank) (hcyc : ¬ IsCyclic c.rhoS) : False := by
  have hSS := c.comm_S_S hR0 hOut
  have hSB := c.comm_S_B hR0 hKD
  obtain ⟨s₁, hs₁, s₂, hs₂, ho₁, ho₂, hcl⟩ := hTwo (Kbar K) c.isSimpleGroup c.exists_ne_comm
    c.isChevTwo c.pRank_top_eq_one c.rhoS c.isPGroup_rhoS hcyc (c.rhoS_inf_inner hR0)
  have hfix : ∀ s ∈ c.rhoS, orderOf s = 2 → ∀ q : Kbar K, s q = q → q ∈ kbarM K M := by
    rintro _ ⟨⟨t, ht⟩, htS, rfl⟩ hord q hq
    have htS' : t ∈ S := mem_subgroupOf.mp htS
    have htO : t ∉ pCoreOf 2 H := fun h => by
      rw [show (⟨t, ht⟩ : ↥H) = ⟨t, c.S_le (c.core_le h)⟩ from rfl,
        c.rho_eq_one_of_mem_core h, orderOf_one] at hord
      omega
    exact c.fix_mem_kbarM hSS hSB htS' htO q hq
  apply c.kbarM_ne_top
  rw [eq_top_iff, ← hcl, closure_le]
  rintro q (hq | hq)
  · exact hfix s₁ hs₁ ho₁ q hq
  · exact hfix s₂ hs₂ ho₂ q hq

end Ctx

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G
