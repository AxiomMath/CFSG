module

public import CFSG.LocalAnalysis.OddStandard.GH71.HBarCent

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G] {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

theorem normal_dichotomy (h : Ctx71 G z S U u) (hB5 : SpecB5)
    {H : Subgroup G} (hSH : S ≤ H)
    (hbar : IsDoubleCoverOfAlt (HBar H) 11 ∨ Blueprint.NativeSporadic.IsSporadic (HBar H) .Ly)
    {L : Subgroup G} (hLH : L ≤ H) (hHL : H ≤ normalizer (L : Set G)) :
    L ≤ pPrimeCoreOf 2 H ⊔ zpowers z ∨ Covers L H (pPrimeCoreOf 2 H) := by
  have hzH : z ∈ H := hSH h.ctx.z_mem
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hπ
  have hLn : (barIn H L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective _ g
    have hg : g' ∈ (H.subgroupOf H) := Subgroup.mem_subgroupOf.mpr g'.2
    have := IVK812.barIn_le_normalizer hHL ⟨g', hg, rfl⟩
    exact (mem_normalizer_iff.mp this n).mp hn
  have hcovL : barIn H L = ⊤ → Covers L H (pPrimeCoreOf 2 H) := by
    intro htop x hx
    have hxL : π ⟨x, hx⟩ ∈ barIn H L := htop ▸ mem_top _
    obtain ⟨l, hl, hle⟩ := hxL
    have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
    have hO : l⁻¹ * ⟨x, hx⟩ ∈ pPrimeCore 2 ↥H := by
      rw [← QuotientGroup.eq_one_iff]
      show π (l⁻¹ * ⟨x, hx⟩) = 1
      rw [map_mul, map_inv, hle, inv_mul_cancel]
    have hOG : ((l⁻¹ * ⟨x, hx⟩ : ↥H) : G) ∈ pPrimeCoreOf 2 H := ⟨_, hO, rfl⟩
    have e : x = (l : G) * ((l⁻¹ * ⟨x, hx⟩ : ↥H) : G) := by simp
    rw [e]
    exact mul_mem (mem_sup_left ⟨hlL, l.2⟩) (mem_sup_right hOG)
  rcases hbar with h11 | hLy
  · rcases hB5 _ h11 _ hLn with hc | htop
    · left
      have hcz := h.zBar_mem_center hSH h11
      have hz1 : zBar H hzH ≠ 1 := by
        intro e; have := h.orderOf_zBar hzH; rw [e, orderOf_one] at this; omega
      intro l hl
      have hlb : π ⟨l, hLH hl⟩ ∈ center (HBar H) := hc ⟨⟨l, hLH hl⟩, hl, rfl⟩
      have hcard : Nat.card (center (HBar H)) = 2 := h11.2.1
      have hzpow : center (HBar H) = zpowers (zBar H hzH) := by
        symm
        refine eq_of_le_of_card_ge (zpowers_le.mpr hcz) ?_
        rw [hcard, Nat.card_zpowers, h.orderOf_zBar]
      rw [hzpow] at hlb
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hlb
      have hO : (⟨z, hzH⟩ ^ k)⁻¹ * ⟨l, hLH hl⟩ ∈ pPrimeCore 2 ↥H := by
        rw [← QuotientGroup.eq_one_iff]
        show π ((⟨z, hzH⟩ ^ k)⁻¹ * ⟨l, hLH hl⟩) = 1
        rw [map_mul, map_inv, map_zpow]
        rw [show π ⟨z, hzH⟩ = zBar H hzH from rfl, hk, inv_mul_cancel]
      have hOG : (((⟨z, hzH⟩ ^ k)⁻¹ * ⟨l, hLH hl⟩ : ↥H) : G) ∈ pPrimeCoreOf 2 H := ⟨_, hO, rfl⟩
      have e : l = z ^ k * (((⟨z, hzH⟩ ^ k)⁻¹ * ⟨l, hLH hl⟩ : ↥H) : G) := by simp
      rw [e, sup_comm]
      exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers z) k)) (mem_sup_right hOG)
    · exact Or.inr (hcovL htop)
  · obtain ⟨e⟩ := hLy
    have : IsSimpleGroup (HBar H) := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.Ly.isSimpleGroup_Ly e
    rcases hLn.eq_bot_or_eq_top with hb | htop
    · left
      exact ((IVK812.barIn_eq_bot_iff hLH).mp hb).trans le_sup_left
    · exact Or.inr (hcovL htop)

end Ctx71

end CFSG.OddStandard.GH71
