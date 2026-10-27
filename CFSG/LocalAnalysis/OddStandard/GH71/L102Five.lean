module

public import CFSG.LocalAnalysis.OddStandard.GH71.HBarIso

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G] {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71


theorem exists_five (h : Ctx71 G z S U u) (hB4 : SpecB4) {H : Subgroup G} (hSH : S ≤ H)
    (hcov : Covers H (Cen z) (pPrimeCoreOf 2 (Cen z)))
    (hbar : IsDoubleCoverOfAlt (HBar H) 11 ∨ Blueprint.NativeSporadic.IsSporadic (HBar H) .Ly)
    {x : HBar H} (hx : orderOf x = 3)
    (hxz : x ∈ centralizer ({zBar H (hSH h.ctx.z_mem)} : Set (HBar H)))
    (hSx : barIn H S ≤ normalizer ((zpowers x : Subgroup (HBar H)) : Set (HBar H))) :
    ∃ g ∈ centralizer ({zBar H (hSH h.ctx.z_mem)} : Set (HBar H)),
      ∃ y ∈ closure ({x, g * x * g⁻¹} : Set (HBar H)), orderOf y = 5 := by
  set C := centralizer ({zBar H (hSH h.ctx.z_mem)} : Set (HBar H)) with hC
  have hK : IsDoubleCoverOfAlt ↥C 11 := h.cover_centralizer_bar hSH hcov hbar
  have hSC : barIn H S ≤ C := fun s hs =>
    mem_centralizer_singleton_iff.mpr (h.zBar_comm hSH s hs)
  set SK := (barIn H S).subgroupOf C with hSK
  have hSK2 : IsPGroup 2 ↥SK := (IVK812.isPGroup_barIn h.S2).comap_subtype
  have hSKcard : Nat.card SK = 2 ^ 8 := by
    rw [← h.card_S, ← IVK812.card_barIn_two hSH h.S2]
    exact Nat.card_congr (subgroupOfEquivOfLe hSC).toEquiv
  set xK : ↥C := ⟨x, hxz⟩ with hxKdef
  have hxK : orderOf xK = 3 := by rw [Subgroup.orderOf_mk]; exact hx
  have hzp : zpowers xK = (zpowers x).subgroupOf C := by
    rw [← Subgroup.comap_map_eq_self_of_injective C.subtype_injective (zpowers xK),
      MonoidHom.map_zpowers]
    rfl
  have hSKn : SK ≤ normalizer ((zpowers xK : Subgroup ↥C) : Set ↥C) := by
    rw [hzp, ← Subgroup.subgroupOf_normalizer_eq (zpowers_le.mpr hxz)]
    intro s hs
    exact hSx hs
  obtain ⟨g, hg1, hg2⟩ := hB4 _ SK hK hSK2 hSKcard xK hxK hSKn
  have hex : ∃ y ∈ closure ({xK, g * xK * g⁻¹} : Set ↥C), orderOf y = 5 := by
    by_contra hne
    push Not at hne
    have hempty : {y : ↥C | y ∈ closure ({xK, g * xK * g⁻¹} : Set ↥C) ∧ orderOf y = 5} = ∅ := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact hne y
    rw [hempty, Subgroup.closure_empty] at hg1
    rw [← hg1, card_bot] at hg2
    norm_num at hg2
  obtain ⟨yK, hyK, hyK5⟩ := hex
  have hmap : (closure ({xK, g * xK * g⁻¹} : Set ↥C)).map C.subtype =
      closure ({x, (g : HBar H) * x * (g : HBar H)⁻¹} : Set (HBar H)) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  refine ⟨g, g.2, yK, ?_, by rw [Subgroup.orderOf_coe]; exact hyK5⟩
  rw [← hmap]
  exact ⟨yK, hyK, rfl⟩

end Ctx71

end CFSG.OddStandard.GH71
