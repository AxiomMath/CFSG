module

public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionQuotient

public section

namespace CFSG.QuasithinUnique.RankOneRecog

open CFSG.Open

theorem rank_one_central_quotient_reconstruction
    {G : Type} [Group G] [Finite G]
    {H S U L : Subgroup G} (hS : IsSylowTwoOf S H) (hUS : U ≤ S) (hU : IsElemAbelian 2 U)
    (hcl : ∀ a ∈ U, ∀ g ∈ H, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ U) (hLH : L ≤ H)
    (hsub : (L.subgroupOf H).IsSubnormal) (hperf : Group.IsPerfect L)
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) (hZ : IsPGroup 2 (Subgroup.center L))
    (hmodel : fusionIsBenderGroup (L ⧸ Subgroup.center L))
    (hw : ∃ w ∈ U, w ∈ Subgroup.centralizer (S : Set G) ∧
      ¬ L ≤ Subgroup.centralizer ({w} : Set G)) :
    Subgroup.center L = ⊥ ∧ IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧
      fusionIsBenderGroup L ∧ ∀ u ∈ U, ∃ x ∈ L, ∀ y ∈ L, u⁻¹ * y * u = x⁻¹ * y * x := by
  have := hperf
  have hinner := central_quotient_action_inner hS hUS hU hcl hLH hperf hUL hmodel
  obtain ⟨w, hwU, hwS, hwnc⟩ := hw
  obtain ⟨P, x, hx, hxn⟩ :=
    exists_noncentral_sylow_centralizer hS hLH hsub hwS (hinner w hwU) hwnc
  have hcenter : Subgroup.center L = ⊥ :=
    center_eq_bot_of_noncentral_sylow_centralizer hZ hmodel P hx hxn
  have hbender : fusionIsBenderGroup L := fusionIsBenderGroup_of_center_eq_bot hcenter hmodel
  exact ⟨hcenter, isSimpleGroup_of_fusionIsBenderGroup hbender,
    exists_noncommuting_of_perfect hbender, hbender, hinner⟩

end CFSG.QuasithinUnique.RankOneRecog
