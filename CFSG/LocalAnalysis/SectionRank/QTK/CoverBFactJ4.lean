module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBMain
public import CFSG.LocalAnalysis.SectionRank.QTK.FactJ4Of
import CFSG.LocalAnalysis.SectionRank.QTK.J4Transfer
import CFSG.Quasithin.Vol2.Ch11SecS12ZQ
public import CFSG.Quasithin.Vol2.Ch11SecS12ZH

public section

namespace CFSG.SectionRank.QTK

open Subgroup

theorem factJ4Inspect_of'
    (hJ : J4ListInspect) : CFSG.Quasithin.Vol2.Ch11.SecS.FactJ4Inspect := by
  intro G _ _ hsimp hnab hqtke X₁ K Lh hX₁ hK hX₁L hLK hperf hSL3 hcomm
  have hq : CFSG.IsQuasisimple ↥K :=
    CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.cfsgQuasisimple_of_gw hK.2.2
  have hKt : K ≠ ⊤ := by
    intro hKt
    have hle : (⊤ : Subgroup G) ≤ normalizer (X₁ : Set G) := hKt ▸ hK.1
    have hXn : X₁.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp hle)
    rcases @Subgroup.Normal.eq_bot_or_eq_top G _ hsimp X₁ hXn with h | h
    · rw [h, card_bot] at hX₁
      omega
    · obtain ⟨a, b, hab⟩ := hnab
      have hG3 : Nat.card G = 3 := by rw [← hX₁, h, card_top]
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcyc : IsCyclic G := isCyclic_of_prime_card hG3
      exact hab ((IsCyclic.isMulCommutative (α := G)).is_comm.comm a b)
  have hKK : CFSG.SectionRank.IsKGroupCat ↥K :=
    CFSG.QuasithinUnique.isKGroupCat_of_kProper hqtke.1 hKt
  have hlist := CoverB.qtkSimpleList_of_cover hqtke.2.2 hq hKK
  have hX₁K : X₁ ≤ K := hX₁L.trans hLK
  have hn : (X₁.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX₁K).mpr hK.1
  have hX₁Z : X₁.subgroupOf K ≤ center ↥K := by
    have hquasi : CFSG.Open.IsQuasisimple ↥K := ⟨hK.2.2.2.1, hK.2.2.2.2⟩
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hquasi
      (X₁.subgroupOf K) with hcent | htop
    · exact hcent
    · exfalso
      have hcard : Nat.card ↥(X₁.subgroupOf K) = 3 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₁K).toEquiv, hX₁]
      have hK3 : Nat.card ↥K = 3 := by rw [← hcard, htop, card_top]
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcyc : IsCyclic ↥K := isCyclic_of_prime_card hK3
      obtain ⟨a, b, hab⟩ := hq.2.2
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (congrArg (QuotientGroup.mk (s := center ↥K))
        ((IsCyclic.isMulCommutative (α := ↥K)).is_comm.comm a b))
  set f : ↥Lh →* ↥K ⧸ center ↥K :=
    (QuotientGroup.mk' (center ↥K)).comp (Subgroup.inclusion hLK) with hf
  have hfker : f.ker ≤ center ↥Lh := by
    intro x hx
    have hx' : Subgroup.inclusion hLK x ∈ center ↥K := (QuotientGroup.eq_one_iff _).mp hx
    rw [mem_center_iff] at hx' ⊢
    intro y
    apply Subgroup.inclusion_injective hLK
    rw [map_mul, map_mul]
    exact hx' (Subgroup.inclusion hLK y)
  have hXker : X₁.subgroupOf Lh ≤ f.ker := fun x hx =>
    (QuotientGroup.eq_one_iff _).mpr
      (hX₁Z (show Subgroup.inclusion hLK x ∈ X₁.subgroupOf K from hx))
  have hXcard : Nat.card ↥(X₁.subgroupOf Lh) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₁L).toEquiv, hX₁]
  have htop : ⁅(⊤ : Subgroup ↥Lh), (⊤ : Subgroup ↥Lh)⁆ = ⊤ := by
    apply Subgroup.map_injective Lh.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hperf]
  have hO : ⁅CFSG.pCore 2 ↥Lh, (⊤ : Subgroup ↥Lh)⁆ ≠ ⊥ := by
    intro hbot
    apply hcomm
    rw [CFSG.Open.pCoreOf]
    have h1 : ⁅(CFSG.pCore 2 ↥Lh).map Lh.subtype, (⊤ : Subgroup ↥Lh).map Lh.subtype⁆ = ⊥ := by
      rw [← map_commutator, hbot, Subgroup.map_bot]
    rwa [← MonoidHom.range_eq_map, range_subtype] at h1
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hSL3
  have hPSL := isPSL_three_two_two_of_central (CFSG.pCore 2 ↥Lh) CFSG.pCore_isPGroup e₀ hF f.ker
    hfker (X₁.subgroupOf Lh) hXcard hXker
  have hsurj := QuotientGroup.mk'_surjective f.ker
  have hLperf : ⁅(⊤ : Subgroup (↥Lh ⧸ f.ker)), (⊤ : Subgroup (↥Lh ⧸ f.ker))⁆ = ⊤ := by
    rw [← MonoidHom.range_eq_top.2 hsurj, MonoidHom.range_eq_map, ← map_commutator, htop]
  have hQcomm : ⁅(CFSG.pCore 2 ↥Lh).map (QuotientGroup.mk' f.ker),
      (⊤ : Subgroup (↥Lh ⧸ f.ker))⁆ ≠ ⊥ := by
    have h := commutator_map_ne_bot htop (QuotientGroup.mk' f.ker)
      (by rw [QuotientGroup.ker_mk']; exact hfker) hO
    rwa [MonoidHom.range_eq_top.2 hsurj] at h
  have hQn : ((CFSG.pCore 2 ↥Lh).map (QuotientGroup.mk' f.ker)).Normal :=
    Subgroup.Normal.map CFSG.pCore_normal _ hsurj
  exact hJ _ hlist (↥Lh ⧸ f.ker) (QuotientGroup.kerLift f) (QuotientGroup.kerLift_injective f)
    hLperf _ (CFSG.pCore_isPGroup.map _) hPSL hQcomm


end CFSG.SectionRank.QTK
