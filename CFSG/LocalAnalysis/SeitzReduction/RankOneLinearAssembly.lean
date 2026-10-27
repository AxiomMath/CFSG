module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearAssemblyElem
public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageChainHKS
public import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearAssemblyEndings

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint CFSG.ABGLocalTools
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974 goldschmidt1974_of_milestone)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem rankOneLinearExclusion_of_inputs
    (hGold : Goldschmidt1974) (hHKS : SmallRootRegularNormalInput)
    (hcase : Endings.GMS43InvolutionCase) : RankOneLinearExclusion := by
  intro G _ _ L hset f hf hL hS2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 (centralizer (L : Set G))) := inferInstance
  have h2 : 2 ∣ Nat.card (centralizer (L : Set G)) := by
    have := Subgroup.card_subgroup_dvd_card (S₀ : Subgroup (centralizer (L : Set G)))
    rwa [hS2 S₀] at this
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (L : Set G)) 2 h2
  have ht : orderOf (c : G) = 2 := by rw [Subgroup.orderOf_coe, hc]
  have htC : (c : G) ∈ centralizer (L : Set G) := c.2
  obtain ⟨P⟩ : Nonempty (Sylow 2 (normalizer (zpowers (c : G) : Set G))) := inferInstance
  set T : Subgroup G := (P : Subgroup _).map (normalizer (zpowers (c : G) : Set G)).subtype
    with hTdef
  have hTN : T ≤ normalizer (zpowers (c : G) : Set G) := map_subtype_le _
  have hT : ∃ P' : Sylow 2 (normalizer (zpowers (c : G) : Set G)),
      (P' : Subgroup _) = T.subgroupOf (normalizer (zpowers (c : G) : Set G)) :=
    ⟨P, (comap_map_eq_self_of_injective (subtype_injective _) _).symm⟩
  have hS : Endings.Setting G L f c T := ⟨hset, hf, hL, hS2, ht, htC, hTN, hT⟩
  obtain ⟨d, -, hdfix, C, m, hch, hm, hsyl⟩ :=
    psl2_pushing_up_sylow_of_goldschmidt hGold hset hf hL ht htC hTN hT hHKS
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain rfl : m = 1 := by omega
    by_cases hel : ∀ x ∈ C 2, x * x = 1
    · exact false_of_chain_of_eq_one_of_elem hGold hHKS hcase hS hch hdfix hel
    · exact false_of_chain_of_eq_one_of_not_elem hGold hS hch hdfix hsyl hel
  · exact false_of_chain_of_two_le hGold hS hch hm2 hdfix hsyl

section Certificates

theorem rankOneLinearExclusion_of_gms43 (hcase : Endings.GMS43InvolutionCase) :
    RankOneLinearExclusion :=
  rankOneLinearExclusion_of_inputs goldschmidt1974_of_milestone smallRootRegularNormalInput hcase

end Certificates

end CFSG.SeitzReduction.RankOne
