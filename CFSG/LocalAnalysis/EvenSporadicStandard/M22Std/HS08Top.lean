module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov7
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Main5
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08KleinB

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem hs08_normal_of_isolated {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
    (hodd : standardComponentOddCore G = ⊥) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hH : centralizer ({t} : Set G) = normalizer (L : Set G))
    (hiso : ∀ g : G, g * t * g⁻¹ ∈ centralizer ({t} : Set G) → g * t * g⁻¹ = t) : L.Normal := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hNn, hNodd, hNg⟩ := CFSG.ZStar.glauberman_zStar G t ht1 ht2
    (fun g hg => hiso g (mem_centralizer_singleton_iff.2 hg))
  have hNle : N ≤ standardComponentOddCore G := le_sSup ⟨hNn, hNodd⟩
  rw [hodd] at hNle
  have hcomm : ∀ g : G, g * t = t * g := by
    intro g
    have h2 : g * t * g⁻¹ * t⁻¹ = 1 := Subgroup.mem_bot.1 (hNle (hNg g))
    have h3 : g * t * g⁻¹ = t := mul_inv_eq_one.1 h2
    calc g * t = (g * t * g⁻¹) * g := by group
      _ = t * g := by rw [h3]
  have hnorm : normalizer (L : Set G) = ⊤ := by
    rw [← hH, eq_top_iff]
    intro g _
    exact mem_centralizer_singleton_iff.2 (hcomm g)
  exact Subgroup.normalizer_eq_top_iff.1 hnorm

theorem haradaSolomon08M22Split_holds :
    HaradaSolomon08M22Split := by
  intro G _ _ L t hodd hstd hq ht hZ hH hrel hy
  have hperf : Group.IsPerfect L := Group.isPerfect_def.2 hstd.1.1
  have ht2 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by decide)
  have htL : t ∈ L := by
    have : t ∈ (center L).map L.subtype := hZ ▸ mem_zpowers t
    obtain ⟨z, -, rfl⟩ := this
    exact z.2
  have hcov : IsM22Cover ↥L ⟨t, htL⟩ :=
    { orderOf_t := by rw [Subgroup.orderOf_mk]; exact ht
      center_eq := by
        apply Subgroup.map_injective L.subtype_injective
        rw [hZ, MonoidHom.map_zpowers]
        rfl
      quotient := hq }
  obtain ⟨y, hyH, hyL, hy2⟩ := hy
  have hyy : y * y = 1 := by rw [← sq, ← hy2]; exact pow_orderOf_eq_one y
  have htC : t ∈ centralizer (L : Set G) :=
    mem_centralizer_iff.2 fun l hl => (congrArg Subtype.val (hcov.t_central ⟨l, hl⟩)).symm
  have hCL : ∀ x ∈ centralizer (L : Set G), x ∈ L → x ∈ zpowers t := by
    intro x hx hxL
    have hxz : (⟨x, hxL⟩ : ↥L) ∈ center ↥L :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (mem_centralizer_iff.1 hx (g : G) g.2)
    rw [← hZ]
    exact Subgroup.mem_map_of_mem L.subtype hxz
  have hCH : ∀ x ∈ centralizer (L : Set G), x ∈ centralizer ({t} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hx t htL).symm
  have hiso : ∀ g : G, g * t * g⁻¹ ∈ centralizer ({t} : Set G) → g * t * g⁻¹ = t := by
    by_cases hC : ∃ c ∈ centralizer (L : Set G), c ∉ zpowers t
    · obtain ⟨c, hcC, hcn⟩ := hC
      have hcL : c ∉ L := fun hcL => hcn (hCL c hcC hcL)
      have hcH : c ∈ centralizer ({t} : Set G) := hCH c hcC
      have hccL : c * c ∈ L := index_two_mul_mem hrel hcH hcH hcL hcL
      have hccC : c * c ∈ centralizer (L : Set G) := (centralizer (L : Set G)).mul_mem hcC hcC
      rcases hs08_eq_one_or_eq (hCL _ hccC hccL) ht2 with hc2 | hc2
      · exact hs08_isolated_klein htL hcov hrel hcC hcL hc2
      · exfalso
        have hcyL : c * y ∈ L := index_two_mul_mem hrel hcH hyH hcL hyL
        have hcl : c * (c * y) = (c * y) * c := (mem_centralizer_iff.1 hcC (c * y) hcyL).symm
        have hl : (c * y) * (c * y) = t := by
          calc (c * y) * (c * y) = ((c * y) * c) * y := by group
            _ = (c * (c * y)) * y := by rw [← hcl]
            _ = (c * c) * (y * y) := by group
            _ = t := by rw [hc2, hyy, mul_one]
        exact hcov.not_sq_t ⟨c * y, hcyL⟩ (Subtype.ext hl)
    · push Not at hC
      have hcen : centralizer (L : Set G) = zpowers t :=
        le_antisymm (fun c hc => hC c hc) (zpowers_le.2 htC)
      have hc : CoverSetting L t :=
        { orderOf_t := ht
          map_center := hZ
          centralizer_L := hcen
          centralizer_t := hH
          relIndex_dvd := by rw [hrel] }
      obtain ⟨e⟩ := hq
      exact hs08_isolated_main hc e ⟨e⟩ hyH hyL hyy
  exact hs08_normal_of_isolated hodd ht1 ht2 hH hiso

end CFSG.EvenSporadicStandard.M22Std
